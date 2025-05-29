use std::{
    ffi::c_void,
    num::NonZeroUsize,
    ops::Range,
    os::fd::{AsFd, OwnedFd},
    ptr::NonNull,
    sync::Arc,
};

use nix::{
    errno::Errno,
    poll::{PollFd, PollFlags, PollTimeout, poll},
    sys::mman::{MRemapFlags, MapFlags, MmapAdvise, ProtFlags},
    unistd::Pid,
    unistd::pipe,
};
use rangemap::RangeMap;
use thiserror::Error;
use util::MmapGuard;

use crate::interceptmem::userfaultfd_ext::UffdExt;

use super::{
    page_addr::{PageAddr, RangeExtLen},
    range_ext::RangeExtOps,
    userfaultfd_ext::{UserfaultFdFlags, userfaultfd_create},
};

use userfaultfd as uffd;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PageFault {
    addr: *mut c_void,
    access: SomePageAccess,
    thread_id: Pid,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PageState {
    Free,
    Mapped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum SomePageAccess {
    ReadOnly,
    ReadWrite,
}
#[allow(dead_code)]
pub type PageAccess = Option<SomePageAccess>;

#[allow(dead_code)]
#[derive(Debug)]
pub struct AddrSpace {
    alive: OwnedFd,
    uffd: Arc<uffd::Uffd>,
    required_ioctls: uffd::IoctlFlags,
    pages: RangeMap<PageAddr, PageState>,
    access: RangeMap<PageAddr, PageAccess>,
}

#[allow(dead_code)]
#[derive(Debug, Error)]
pub enum AddrSpaceError {
    #[error("Invalid range: {msg}")]
    InvalidRange { msg: String },

    #[error("Invalid flags: {msg}")]
    InvalidFlags { msg: String },

    #[error("Insufficient capacity")]
    InsufficientCapacity,

    #[error("Runtime error ({errno}): {msg}")]
    RuntimeError { msg: String, errno: Errno },
}

impl AddrSpace {
    #[allow(dead_code)]
    pub fn new(user_mode_only: bool) -> Result<(AddrSpace, AddrSpaceEngine), AddrSpaceError> {
        let required_features = uffd::FeatureFlags::PAGEFAULT_FLAG_WP
            .union(uffd::FeatureFlags::THREAD_ID)
            .union(uffd::FeatureFlags::EVENT_REMAP);
        let required_ioctls = uffd::IoctlFlags::REGISTER
            .union(uffd::IoctlFlags::UNREGISTER)
            .union(uffd::IoctlFlags::API);

        let uffd = Arc::new(
            userfaultfd_create(
                UserfaultFdFlags {
                    user_mode_only,
                    non_blocking: true,
                    close_on_exec: false,
                },
                required_features,
                required_ioctls,
            )
            .unwrap(),
        );

        let (alive_rx, alive_tx) = pipe().map_err(|errno| AddrSpaceError::RuntimeError {
            msg: "pipe creation failed".into(),
            errno,
        })?;

        let required_ioctls = uffd::IoctlFlags::WAKE
            .union(uffd::IoctlFlags::COPY)
            .union(uffd::IoctlFlags::ZEROPAGE)
            .union(uffd::IoctlFlags::WRITE_PROTECT);
        let addrspace = AddrSpace {
            alive: alive_tx,
            uffd: uffd.clone(),
            required_ioctls,
            pages: Default::default(),
            access: Default::default(),
        };
        let fault_receiver = AddrSpaceEngine { alive: alive_rx, uffd };
        Ok((addrspace, fault_receiver))
    }

    /// Reserves a range of pages of the specified length for address space use.
    ///
    /// # Returns
    ///
    /// Returns a `Range<PageAddr>` representing the reserved range if successful,
    /// otherwise returns an error.
    #[allow(dead_code)]
    pub fn reserve_any(&mut self, length: NonZeroUsize) -> Result<Range<PageAddr>, AddrSpaceError> {
        let mmapped =
            unsafe { nix::sys::mman::mmap_anonymous(None, length, ProtFlags::PROT_NONE, MapFlags::MAP_PRIVATE) }
                .map_err(|errno| AddrSpaceError::RuntimeError {
                    msg: format!("mmap_anonymous(len: {}) failed", length),
                    errno,
                })?;
        let mmapped = unsafe { util::MmapGuard::from_raw(mmapped, length) };

        let reserved = PageAddr::try_from(mmapped.addr()).expect("mmap_anonymous should've returned a page address");
        let reserved = reserved
            .enclosing_range(mmapped.length())
            .expect("mmap_anonymous should've returned pages that can be represented by the PageAddr");

        assert!(!self.pages.overlaps(&reserved));
        self.pages.insert(reserved.clone(), PageState::Free);
        mmapped.consume(); // `self` now owns this range
        Ok(reserved)
    }

    /// Reserves the specified range of pages for address space use.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn reserve(&mut self, range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        if self.pages.overlaps(range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: format!("part of the {:?} range already reserved", range),
            });
        }

        let addr: NonNull<c_void> = range.start.into();
        let addr: NonZeroUsize = (addr.as_ptr() as usize).try_into().expect("non-null ptr is non-0");
        let length = range.len();
        let mmapped = unsafe {
            nix::sys::mman::mmap_anonymous(
                Some(addr),
                length,
                ProtFlags::PROT_NONE,
                MapFlags::MAP_PRIVATE.union(MapFlags::MAP_FIXED_NOREPLACE),
            )
        }
        .map_err(|errno| AddrSpaceError::RuntimeError {
            msg: format!("mmap_anonymous(range: {:?}) failed", range),
            errno,
        })?;
        let mmapped = unsafe { util::MmapGuard::from_raw(mmapped, length) };

        let reserved = PageAddr::try_from(mmapped.addr()).expect("mmap_anonymous should've returned a page address");
        let reserved = reserved
            .enclosing_range(mmapped.length())
            .expect("mmap_anonymous should've returned pages that can be represented by the PageAddr");

        self.pages.insert(reserved, PageState::Free);
        mmapped.consume(); // `self` now owns this range
        Ok(())
    }

    /// Releases a previously reserved range of pages from address space.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn release(&mut self, _range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        todo!()
    }

    fn find_free(&self, length: NonZeroUsize) -> Option<Range<PageAddr>> {
        self.pages.iter().find_map(|(pages, state)| {
            if pages.len() >= length && *state == PageState::Free {
                Some(
                    pages
                        .start
                        .enclosing_range(length)
                        .expect("enclosing range should fit into reserved"),
                )
            } else {
                None
            }
        })
    }

    fn is_reserved(&self, range: &Range<PageAddr>) -> bool {
        self.pages.gaps(range).next().is_none()
    }

    fn get_state(&self, range: &Range<PageAddr>) -> Option<&PageState> {
        let (pages, state) = self.pages.get_key_value(&range.start)?;
        if pages.encloses(range) { Some(state) } else { None }
    }

    fn is_free(&self, range: &Range<PageAddr>) -> bool {
        self.get_state(range).is_some_and(|state| *state == PageState::Free)
    }

    fn is_mapped(&self, range: &Range<PageAddr>) -> bool {
        self.get_state(range).is_some_and(|state| *state == PageState::Mapped)
    }

    fn get_access(&self, range: &Range<PageAddr>) -> Option<&PageAccess> {
        let (pages, access) = self.access.get_key_value(&range.start)?;
        if pages.encloses(range) { Some(access) } else { None }
    }

    fn has_none_access(&self, range: &Range<PageAddr>) -> bool {
        self.get_access(range).is_some_and(|access| access.is_none())
    }

    fn has_some_access(&self, range: &Range<PageAddr>) -> bool {
        self.is_mapped(range) && self.access.overlapping(range).all(|(_pages, access)| access.is_some())
    }

    /// Maps a previously reserved range of pages of the specified length as anonymous memory.
    ///
    /// # Warning
    ///
    /// Initially, mapped range doesn't have access, and any access would cause a fault.
    /// In order to resolve the fault, access has to be given.
    ///
    /// # Returns
    ///
    /// Returns a `Range<PageAddr>` representing the mapped range if successful,
    /// otherwise returns an error.
    #[allow(dead_code)]
    pub fn map_anonymous_any(
        &mut self,
        length: NonZeroUsize,
        prot: ProtFlags,
        flags: MapFlags,
    ) -> Result<Range<PageAddr>, AddrSpaceError> {
        if flags.contains(MapFlags::MAP_FIXED) || flags.contains(MapFlags::MAP_FIXED_NOREPLACE) {
            return Err(AddrSpaceError::InvalidFlags {
                msg: "MAP_FIXED and MAP_FIXED_NOREPLACE flags invalid without specified range".into(),
            });
        }

        if let Some(free) = self.find_free(length) {
            self.map_anonymous(&free, prot, flags.union(MapFlags::MAP_FIXED))?;
            Ok(free)
        } else {
            Err(AddrSpaceError::InsufficientCapacity)
        }
    }

    /// Maps the specified range of reserved pages as anonymous memory.
    ///
    /// # Warning
    ///
    /// Initially, mapped range doesn't have access, and any access would cause a fault.
    /// In order to resolve the fault, access has to be given.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn map_anonymous(
        &mut self,
        range: &Range<PageAddr>,
        prot: ProtFlags,
        flags: MapFlags,
    ) -> Result<Range<PageAddr>, AddrSpaceError> {
        if flags.contains(MapFlags::MAP_FIXED) && flags.contains(MapFlags::MAP_FIXED_NOREPLACE) {
            return Err(AddrSpaceError::InvalidFlags {
                msg: "MAP_FIXED and MAP_FIXED_NOREPLACE flags are mutually exclusive".into(),
            });
        }

        // Desired pages are `mmap`ped and setup out of place, and then
        // `mremap`ped into place.
        //
        // This is in order to make mapping atomic:
        // - if any of the calls fails during the setup, bail out without any
        //   changes to the address space
        // - moving pages into place is done using `mremap`, which is atomic

        // `mmap` with `PROT_NONE`, so that no one has access to the `mmapped`
        // pages while they're setup.
        // Real `prot` flags are applied after the `mmapped` pages have been
        // registered to the userfaultfd.
        let mmapped = unsafe {
            nix::sys::mman::mmap_anonymous(
                None,
                range.len(),
                ProtFlags::PROT_NONE,
                flags
                    .difference(MapFlags::MAP_FIXED)
                    .difference(MapFlags::MAP_FIXED_NOREPLACE),
            )
        }
        .map_err(|errno| AddrSpaceError::RuntimeError {
            msg: format!("mmap_anonymous(len: {}) failed", range.len()),
            errno,
        })?;
        let mmapped = unsafe { util::MmapGuard::from_raw(mmapped, range.len()) };
        let supported_ioctls = self
            .uffd
            .register_with_mode(
                mmapped.addr().as_ptr(),
                mmapped.length().get(),
                uffd::RegisterMode::MISSING.union(uffd::RegisterMode::WRITE_PROTECT),
            )
            .map_err(|err| AddrSpaceError::RuntimeError {
                msg: format!("failed registering pages with the userfaultfd: {}", err),
                errno: Errno::UnknownErrno,
            })?;
        assert!(supported_ioctls.contains(self.required_ioctls));
        // Ensure that `mmapped` is protected by userfaultfd
        unsafe { nix::sys::mman::madvise(mmapped.addr(), mmapped.length().get(), MmapAdvise::MADV_DONTNEED) }.map_err(
            |errno| AddrSpaceError::RuntimeError {
                msg: "madvise failed dropping the pages".into(),
                errno,
            },
        )?;
        unsafe { nix::sys::mman::mprotect(mmapped.addr(), mmapped.length().get(), prot) }.map_err(|errno| {
            AddrSpaceError::RuntimeError {
                msg: "mprotect failed applying the desired prot".into(),
                errno,
            }
        })?;

        // Try to move `mmapped` pages to the specified `range`.
        if self.is_free(range) || (flags.contains(MapFlags::MAP_FIXED) && self.is_reserved(range)) {
            let mremaped = unsafe {
                nix::sys::mman::mremap(
                    mmapped.addr(),
                    mmapped.length().get(),
                    mmapped.length().get(),
                    MRemapFlags::MREMAP_FIXED.union(MRemapFlags::MREMAP_MAYMOVE),
                    Some(range.start.into()),
                )
            }
            .map_err(|errno| AddrSpaceError::RuntimeError {
                msg: format!("mremap failed to move pages into the {:?} range", range),
                errno,
            })?;
            assert_eq!(mremaped, range.start.into());
            self.pages.insert(range.clone(), PageState::Mapped);
            self.access.insert(range.clone(), None);
            let _ = mmapped.consume(); // `self` now owns this range
            return Ok(range.clone());
        }

        if flags.contains(MapFlags::MAP_FIXED) || flags.contains(MapFlags::MAP_FIXED_NOREPLACE) {
            if !self.is_reserved(range) {
                return Err(AddrSpaceError::InvalidRange {
                    msg: "part of the range not reserved".into(),
                });
            }
            assert!(!flags.contains(MapFlags::MAP_FIXED)); // this is impossible
            return Err(AddrSpaceError::RuntimeError {
                msg: "part of the range already mapped".into(),
                errno: Errno::EEXIST,
            });
        }

        // Retry `map_anonymous_any` for non-fixed mappings
        self.map_anonymous_any(range.len(), prot, flags)
    }

    /// Unmaps a previously mapped range of pages.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn unmap(&mut self, _range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        todo!()
    }

    /// Gives access to a previously mapped range of pages that doesn't have access.
    ///
    /// `data` is the new content of the pages.
    ///
    /// If `data` is:
    /// - `None`, pages are initialized with zeros
    /// - `Some(&[u8])`, pages are initialized with the provided content, which has to
    ///   match the size of the `range`
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn give_access(
        &mut self,
        range: &Range<PageAddr>,
        access: SomePageAccess,
        data: Option<&[u8]>,
    ) -> Result<(), AddrSpaceError> {
        if let Some(data) = data {
            if data.len() != range.len().get() {
                return Err(AddrSpaceError::InvalidRange {
                    msg: "range and data has to have the same length".into(),
                });
            }
        }

        if !self.has_none_access(range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: "part of the range not reserved, not mapped or already has access".into(),
            });
        }

        let addr = NonNull::from(range.start).as_ptr();
        let length = range.len().get();
        if let Some(data) = data {
            let copied = unsafe {
                self.uffd.copy_with_wp(
                    data.as_ptr() as *mut _,
                    addr,
                    length,
                    true,
                    access == SomePageAccess::ReadOnly,
                )
            }
            .map_err(|err| AddrSpaceError::RuntimeError {
                msg: format!("userfaultfd copy failed with: {}", err),
                errno: Errno::UnknownErrno,
            })?;
            assert_eq!(copied, length);
        } else {
            match access {
                SomePageAccess::ReadOnly => {
                    // `zeropage` doesn't have WP mode. Copy instead.
                    // TODO: `zeropage` and `writeprotect` out of place, then move into place
                    let zeros = unsafe {
                        nix::sys::mman::mmap_anonymous(None, range.len(), ProtFlags::PROT_READ, MapFlags::MAP_PRIVATE)
                            .map_err(|errno| AddrSpaceError::RuntimeError {
                                msg: "mmap failed creating zeroed buffer".into(),
                                errno,
                            })
                    }?;
                    let zeros = unsafe { MmapGuard::from_raw(zeros, range.len()) };
                    let copied = unsafe { self.uffd.copy_with_wp(zeros.addr().as_ptr(), addr, length, true, true) }
                        .map_err(|err| AddrSpaceError::RuntimeError {
                            msg: format!("userfaultfd copy failed with: {}", err),
                            errno: Errno::UnknownErrno,
                        })?;
                    assert_eq!(copied, length);
                }
                SomePageAccess::ReadWrite => {
                    let zeroed = unsafe { self.uffd.zeropage(addr, length, true) }.map_err(|err| {
                        AddrSpaceError::RuntimeError {
                            msg: format!("userfaultfd zeropage failed with: {}", err),
                            errno: Errno::UnknownErrno,
                        }
                    })?;
                    assert_eq!(zeroed, length);
                }
            }
        }
        self.access.insert(range.clone(), Some(access));
        Ok(())
    }

    /// Updates access to a previously mapped range of pages that has some access.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn update_access(&mut self, _range: &Range<PageAddr>, _access: SomePageAccess) -> Result<(), AddrSpaceError> {
        todo!()
    }

    /// Takes the access from a previously mapped range of pages that has some access.
    ///
    /// # Warning
    ///
    /// By taking the access, content of the pages is dropped.
    /// Copy the content of the pages if needed before taking the access.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn take_access(&mut self, range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        if !self.has_some_access(range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: "part of the range doesn't have access".into(),
            });
        }

        unsafe { nix::sys::mman::madvise(range.start.into(), range.len().get(), MmapAdvise::MADV_DONTNEED) }.map_err(
            |errno| AddrSpaceError::RuntimeError {
                msg: "madvise failed dropping the pages".into(),
                errno,
            },
        )?;
        self.access.insert(range.clone(), None);
        Ok(())
    }
}

#[allow(dead_code)]
pub struct AddrSpaceEngine {
    alive: OwnedFd,
    uffd: Arc<uffd::Uffd>,
}

#[allow(dead_code)]
#[derive(Debug, Error)]
pub enum AddrSpaceEngineError {
    #[error("Fault handler error ({errno})")]
    FaultHandlerError { errno: Errno },

    #[error("Generic runtime error ({errno}): {msg}")]
    RuntimeError { msg: String, errno: Errno },
}

impl AddrSpaceEngine {
    #[allow(dead_code)]
    pub fn run<F>(&mut self, fault_handler: F) -> Result<(), AddrSpaceEngineError>
    where
        F: Fn(PageFault) -> Result<(), Errno>,
    {
        let mut fds = [
            PollFd::new(self.uffd.as_fd(), PollFlags::POLLIN),
            PollFd::new(self.alive.as_fd(), PollFlags::empty()),
        ];
        let mut events_buf = uffd::EventBuffer::new(1024);
        loop {
            loop {
                let mut num_unhandled_revents = match poll(&mut fds, PollTimeout::NONE) {
                    Ok(ret) => {
                        assert!(ret >= 0, "poll shouldn't have failed");
                        assert_ne!(ret, 0, "poll shouldn't have timeouted");
                        ret
                    }
                    Err(errno) => {
                        match errno {
                            Errno::EINTR => continue, // retry if poll is interrupted
                            _ => {
                                return Err(AddrSpaceEngineError::RuntimeError {
                                    msg: "polling userfaultfd failed".into(),
                                    errno,
                                });
                            }
                        }
                    }
                };

                let uffd_fd = &mut fds[0];
                if let Some(mut revents) = uffd_fd.revents() {
                    if revents.contains(PollFlags::POLLIN) {
                        revents.remove(PollFlags::POLLIN);
                        num_unhandled_revents -= 1;
                    }
                    assert!(revents.is_empty(), "should've received only POLLIN");
                }
                match num_unhandled_revents {
                    0 => break,         // only POLLIN revent from the userfaultfd is received
                    1 => return Ok(()), // unhandled event is from the `self.alive`, which means that AddrSpace is dropped
                    _ => panic!("shouldn't have more than 1 unhandled revent"),
                }
            }

            let events = self
                .uffd
                .read_events(&mut events_buf)
                .map_err(|err| AddrSpaceEngineError::RuntimeError {
                    msg: format!("userfaultfd failed during event read: {}", err),
                    errno: Errno::UnknownErrno,
                })?;
            for event in events {
                let event = event.map_err(|err| AddrSpaceEngineError::RuntimeError {
                    msg: format!("userfaultfd event error: {}", err),
                    errno: Errno::UnknownErrno,
                })?;
                match event {
                    uffd::Event::Pagefault {
                        kind: _,
                        rw,
                        addr,
                        thread_id,
                    } => {
                        let access = if rw == uffd::ReadWrite::Write {
                            SomePageAccess::ReadWrite
                        } else {
                            SomePageAccess::ReadOnly
                        };
                        fault_handler(PageFault {
                            addr,
                            access,
                            thread_id: Pid::from_raw(thread_id.as_raw()),
                        })
                        .map_err(|errno| AddrSpaceEngineError::FaultHandlerError { errno })?;
                        continue;
                    }
                    uffd::Event::Remap { .. } => {
                        // Just receive `Remap` event to unblock the `mremap` caller
                        continue;
                    }
                    _ => panic!("shouldn't have received any other event"),
                }
            }
        }
    }
}

mod util {
    use std::{ffi::c_void, num::NonZeroUsize, ptr::NonNull};

    /// Guard for `nix::sys::mman::mmap`ped range of pages.
    pub(super) struct MmapGuard(Option<(NonNull<c_void>, NonZeroUsize)>);
    impl MmapGuard {
        pub unsafe fn from_raw(addr: NonNull<c_void>, length: NonZeroUsize) -> Self {
            Self(Some((addr, length)))
        }
        pub fn addr(&self) -> NonNull<c_void> {
            self.0.expect("invariant: inner data is Some until consumed").0
        }
        pub fn length(&self) -> NonZeroUsize {
            self.0.expect("invariant: inner data is Some until consumed").1
        }
        pub fn consume(mut self) -> (NonNull<c_void>, NonZeroUsize) {
            self.0.take().expect("invariant: inner data is Some until consumed")
        }
    }
    impl Drop for MmapGuard {
        fn drop(&mut self) {
            if let Some((addr, length)) = self.0 {
                unsafe {
                    nix::sys::mman::munmap(addr, length.get()).expect("munmap should've succeeded on mmapped range")
                };
            }
        }
    }
}

impl Drop for AddrSpace {
    fn drop(&mut self) {
        for (range, _state) in self.pages.iter() {
            unsafe {
                nix::sys::mman::munmap(range.start.into(), range.len().get())
                    .expect("munmap should've succeeded on reserved range");
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        sync::{
            RwLock,
            atomic::{AtomicUsize, Ordering},
        },
        thread,
    };

    use crate::interceptmem::{addr_space::util::MmapGuard, page_addr::PAGE_SIZE};

    use super::*;

    #[test]
    fn test_addr_space_reserve_any() {
        let (mut addrspace, _fault_receiver) = AddrSpace::new(true).unwrap();
        let reserved = addrspace.reserve_any(1.try_into().unwrap()).unwrap();
        assert_eq!(reserved.len().get(), PAGE_SIZE);

        let inner_reserved = addrspace.pages.get_key_value(&reserved.start).unwrap();
        assert_eq!(*inner_reserved.0, reserved);
        assert_eq!(*inner_reserved.1, PageState::Free);
    }

    #[test]
    fn test_addr_space_reserve() {
        let mmapped = unsafe {
            nix::sys::mman::mmap_anonymous(
                None,
                PAGE_SIZE.try_into().unwrap(),
                ProtFlags::PROT_NONE,
                MapFlags::MAP_PRIVATE,
            )
            .unwrap()
        };
        let mmapped = unsafe { MmapGuard::from_raw(mmapped, PAGE_SIZE.try_into().unwrap()) };
        let occupied: PageAddr = mmapped.addr().try_into().unwrap();
        let occupied = occupied.enclosing_range(mmapped.length()).unwrap();

        let (mut addrspace, _fault_receiver) = AddrSpace::new(true).unwrap();

        // AddrSpace shouldn't reserve externally mmapped range
        let result = addrspace.reserve(&occupied);
        assert!(result.is_err());
    }

    #[test]
    fn test_addr_space_mmap_any() {
        let (addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let addrspace = Arc::new(RwLock::new(addrspace));

        let fault_counter = Arc::new(AtomicUsize::new(0));

        let addrspace_weak = Arc::downgrade(&addrspace);
        let fault_counter_clone = fault_counter.clone();
        let engine_thread = thread::spawn(move || {
            engine
                .run(|pagefault| {
                    println!("Got {:?}", pagefault);
                    let fault_counter = fault_counter_clone.fetch_add(1, Ordering::Relaxed);

                    let addrspace = if let Some(addrspace) = addrspace_weak.upgrade() {
                        addrspace
                    } else {
                        println!("AddrSpace is dropped");
                        return Ok(());
                    };

                    let addr = PageAddr::containing_page(NonNull::new(pagefault.addr).unwrap()).unwrap();
                    let range = addr.enclosing_range(NonZeroUsize::new(1).unwrap()).unwrap();

                    match fault_counter {
                        0 => {
                            let data: [u8; PAGE_SIZE] = [42; PAGE_SIZE];
                            addrspace
                                .write()
                                .unwrap()
                                .give_access(&range, SomePageAccess::ReadWrite, Some(&data))
                                .unwrap();
                        }
                        _ => panic!("shouldn't have happened"),
                    }
                    Ok(())
                })
                .unwrap();
        });

        let reserved = addrspace
            .write()
            .unwrap()
            .reserve_any((10 * PAGE_SIZE).try_into().unwrap())
            .unwrap();
        let mmapped = addrspace
            .write()
            .unwrap()
            .map_anonymous_any(
                reserved.len(),
                ProtFlags::PROT_READ.union(ProtFlags::PROT_WRITE),
                MapFlags::MAP_PRIVATE,
            )
            .unwrap();
        assert_eq!(reserved, mmapped);

        let val_ptr = NonNull::from(mmapped.start).as_ptr() as *mut u8;
        let val = unsafe { *(val_ptr) };
        assert_eq!(val, 42);

        drop(addrspace);
        engine_thread.join().unwrap();
        assert_eq!(fault_counter.load(Ordering::Relaxed), 1);
    }
}
