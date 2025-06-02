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
    page_addr::{PAGE_SIZE, PageAddr, RangeExtLen},
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

    /// Releases a previously reserved (but not mapped) range of pages from address space.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn release(&mut self, range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        if !self.is_free(range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: "range is not free".into(),
            });
        }
        unsafe { nix::sys::mman::munmap(range.start.into(), range.len().get()) }.map_err(|errno| {
            AddrSpaceError::RuntimeError {
                msg: "munmap failed during release".into(),
                errno,
            }
        })?;

        self.pages.remove(range.clone());
        Ok(())
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

    fn has_ro_access(&self, range: &Range<PageAddr>) -> bool {
        self.is_mapped(range)
            && self
                .access
                .overlapping(range)
                .all(|(_pages, access)| *access == Some(SomePageAccess::ReadOnly))
    }

    fn has_rw_access(&self, range: &Range<PageAddr>) -> bool {
        self.is_mapped(range)
            && self
                .access
                .overlapping(range)
                .all(|(_pages, access)| *access == Some(SomePageAccess::ReadWrite))
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
        if !flags.contains(MapFlags::MAP_PRIVATE) {
            return Err(AddrSpaceError::InvalidFlags {
                msg: "only private memory is supported".into(),
            });
        }
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
    pub fn unmap(&mut self, range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        let to_unmap = RangeMap::from_iter(
            self.pages
                .overlapping(range)
                .map(|(pages, _state)| (pages.intersection(range), ())),
        );
        for (range, _) in to_unmap {
            unsafe {
                nix::sys::mman::mmap_anonymous(
                    Some(NonZeroUsize::new(NonNull::from(range.start).as_ptr() as usize).unwrap()),
                    range.len(),
                    ProtFlags::PROT_NONE,
                    MapFlags::MAP_PRIVATE.union(MapFlags::MAP_FIXED),
                )
            }
            .expect("shouldn't have failed, otherwise unrecoverable error");
            self.pages.insert(range.clone(), PageState::Free);
            self.access.remove(range);
        }
        Ok(())
    }

    /// Protects a previously mapped range of pages.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn protect(&mut self, range: &Range<PageAddr>, prot: ProtFlags) -> Result<(), AddrSpaceError> {
        if !self.is_mapped(range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: "range is not mapped".into(),
            });
        }
        unsafe { nix::sys::mman::mprotect(NonNull::from(range.start), range.len().get(), prot) }.map_err(|errno| {
            AddrSpaceError::RuntimeError {
                msg: "mprotect failed".into(),
                errno,
            }
        })
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

    /// Upgrades access from a previously mapped range of pages that has
    /// `SomePageAccess::ReadOnly` access into `SomePageAccess::ReadWrite`.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn upgrade_access(&mut self, range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        if !self.has_ro_access(range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: "part of the range doesn't have RO access".into(),
            });
        }
        self.uffd
            .remove_write_protection(NonNull::from(range.start).as_ptr(), range.len().get(), true)
            .map_err(|err| AddrSpaceError::RuntimeError {
                msg: format!("userfaultfd remove_write_protection failed with: {}", err),
                errno: Errno::UnknownErrno,
            })?;
        self.access.insert(range.clone(), Some(SomePageAccess::ReadWrite));
        Ok(())
    }

    /// Downgrades access from a previously mapped range of pages that has
    /// `SomePageAccess::ReadWrite` access into `SomePageAccess::ReadOnly`.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn downgrade_access(&mut self, range: &Range<PageAddr>) -> Result<(), AddrSpaceError> {
        if !self.has_rw_access(range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: "part of the range doesn't have RW access".into(),
            });
        }
        self.uffd
            .write_protect(NonNull::from(range.start).as_ptr(), range.len().get())
            .map_err(|err| AddrSpaceError::RuntimeError {
                msg: format!("userfaultfd write_protect failed with: {}", err),
                errno: Errno::UnknownErrno,
            })?;
        self.access.insert(range.clone(), Some(SomePageAccess::ReadOnly));
        Ok(())
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

    /// Consumes pagefault causing the blocked thread to retry the access that
    /// caused the pagefault.
    ///
    /// This comes handy if `AddrSpace` has changed after the pagefault has
    /// happened, but before it has been handled.
    /// For example:
    /// 1. thread_a causes a pagefault
    /// 2. pagefault handler receives the thread_a pagefault
    /// 3. thread_b causes the same pagefault
    /// 4. pagefault handler handles thread_a pagefault
    /// 5. pagefault handler receives the thread_b pagefault => fault is already
    ///    handled, just consume it
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn consume_pagefault(&self, pagefault: PageFault) -> Result<(), AddrSpaceError> {
        let addr = if let Some(addr) = NonNull::new(pagefault.addr) {
            addr
        } else {
            return Err(AddrSpaceError::InvalidRange {
                msg: "pagefault address NULL is invalid".into(),
            });
        };
        let addr = if let Some(addr) = PageAddr::containing_page(addr) {
            addr
        } else {
            return Err(AddrSpaceError::InvalidRange {
                msg: "pagefault address is invalid".into(),
            });
        };

        // If `access` is `None`, it means that `addr` points to the free page.
        // Such access won't cause UFFD pagefault, but raise SIGSEGV - that's fine.
        if let Some(access) = self.access.get(&addr) {
            if *access < Some(pagefault.access) {
                return Err(AddrSpaceError::InvalidRange {
                    msg: "pagefault shouldn't be consumed".into(),
                });
            }
        }
        self.uffd
            .wake(NonNull::from(addr).as_ptr(), PAGE_SIZE)
            .map_err(|err| AddrSpaceError::RuntimeError {
                msg: format!("userfaultfd wake failed with: {}", err),
                errno: Errno::UnknownErrno,
            })
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

    use crate::interceptmem::{addr_space::util::MmapGuard, mem_ops::NonFaultingMemOps, page_addr::PAGE_SIZE};

    use super::*;

    #[test]
    fn test_addr_space_reserve_release() {
        let (mut addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let engine_thread = thread::spawn(move || {
            engine.run(|_pagefault| Ok(())).unwrap();
        });

        let reserved = addrspace.reserve_any(1.try_into().unwrap()).unwrap();
        assert_eq!(reserved.len().get(), PAGE_SIZE);
        assert!(addrspace.access.is_empty());
        {
            let pages = Vec::from_iter(addrspace.pages.iter().map(|(pages, state)| (pages.clone(), *state)));
            let pages_expected = [(reserved.clone(), PageState::Free)];
            assert_eq!(pages, pages_expected);
        }

        addrspace.release(&reserved).unwrap();
        assert!(addrspace.pages.is_empty());
        assert!(addrspace.access.is_empty());

        drop(addrspace);
        engine_thread.join().unwrap();
    }

    #[test]
    fn test_addr_space_reserve_doesnt_unmap_external() {
        let mapped = unsafe {
            nix::sys::mman::mmap_anonymous(
                None,
                PAGE_SIZE.try_into().unwrap(),
                ProtFlags::PROT_NONE,
                MapFlags::MAP_PRIVATE,
            )
            .unwrap()
        };
        let mapped = unsafe { MmapGuard::from_raw(mapped, PAGE_SIZE.try_into().unwrap()) };
        let external: PageAddr = mapped.addr().try_into().unwrap();
        let external = external.enclosing_range(mapped.length()).unwrap();

        let (mut addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let engine_thread = thread::spawn(move || {
            engine.run(|_pagefault| Ok(())).unwrap();
        });

        // AddrSpace shouldn't reserve externally mapped range
        let result = addrspace.reserve(&external);
        assert!(result.is_err());
        assert!(addrspace.pages.is_empty());
        assert!(addrspace.access.is_empty());

        drop(addrspace);
        engine_thread.join().unwrap();
    }

    #[test]
    fn test_addr_space_map_unmap() {
        let (mut addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let engine_thread = thread::spawn(move || {
            engine.run(|_pagefault| Ok(())).unwrap();
        });

        assert!(
            addrspace
                .map_anonymous_any(
                    PAGE_SIZE.try_into().unwrap(),
                    ProtFlags::PROT_NONE,
                    MapFlags::MAP_PRIVATE
                )
                .is_err()
        );

        let reserved = addrspace.reserve_any(PAGE_SIZE.try_into().unwrap()).unwrap();
        let mapped = addrspace
            .map_anonymous_any(
                PAGE_SIZE.try_into().unwrap(),
                ProtFlags::PROT_NONE,
                MapFlags::MAP_PRIVATE,
            )
            .unwrap();
        assert_eq!(mapped, reserved);

        {
            let pages = Vec::from_iter(addrspace.pages.iter().map(|(pages, state)| (pages.clone(), *state)));
            let pages_expected = [(mapped.clone(), PageState::Mapped)];
            assert_eq!(pages, pages_expected);

            let access = Vec::from_iter(addrspace.access.iter().map(|(pages, access)| (pages.clone(), *access)));
            let access_expected = [(mapped.clone(), None::<SomePageAccess>)];
            assert_eq!(access, access_expected);
        }

        addrspace.unmap(&mapped).unwrap();
        {
            let pages = Vec::from_iter(addrspace.pages.iter().map(|(pages, state)| (pages.clone(), *state)));
            let pages_expected = [(mapped.clone(), PageState::Free)];
            assert_eq!(pages, pages_expected);

            assert!(addrspace.access.is_empty());
        }

        drop(addrspace);
        engine_thread.join().unwrap();
    }

    #[test]
    fn test_addr_space_map_doesnt_unmap_external() {
        let mapped = unsafe {
            nix::sys::mman::mmap_anonymous(
                None,
                PAGE_SIZE.try_into().unwrap(),
                ProtFlags::PROT_NONE,
                MapFlags::MAP_PRIVATE,
            )
            .unwrap()
        };
        let mapped = unsafe { MmapGuard::from_raw(mapped, PAGE_SIZE.try_into().unwrap()) };
        let external: PageAddr = mapped.addr().try_into().unwrap();
        let external = external.enclosing_range(mapped.length()).unwrap();

        let (mut addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let engine_thread = thread::spawn(move || {
            engine.run(|_pagefault| Ok(())).unwrap();
        });

        // AddrSpace shouldn't map over externally mapped range
        let result = addrspace.map_anonymous(
            &external,
            ProtFlags::PROT_NONE,
            MapFlags::MAP_PRIVATE.union(MapFlags::MAP_FIXED),
        );
        assert!(result.is_err());
        assert!(addrspace.pages.is_empty());
        assert!(addrspace.access.is_empty());

        drop(addrspace);
        engine_thread.join().unwrap();
    }

    #[test]
    fn test_addr_space_protect() {
        let (mut addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let engine_thread = thread::spawn(move || {
            engine.run(|_pagefault| Ok(())).unwrap();
        });

        addrspace.reserve_any(PAGE_SIZE.try_into().unwrap()).unwrap();
        let mapped = addrspace
            .map_anonymous_any(
                PAGE_SIZE.try_into().unwrap(),
                ProtFlags::PROT_NONE,
                MapFlags::MAP_PRIVATE,
            )
            .unwrap();
        addrspace.give_access(&mapped, SomePageAccess::ReadWrite, None).unwrap();

        let mut mem_ops = NonFaultingMemOps::new().unwrap();
        let mut mem_ops_tmp_buf = [0u8];

        // Initially, page is PROT_NONE
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );

        addrspace.protect(&mapped, ProtFlags::PROT_READ).unwrap();
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Ok(mem_ops_tmp_buf.len())
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );

        addrspace
            .protect(&mapped, ProtFlags::PROT_READ.union(ProtFlags::PROT_WRITE))
            .unwrap();
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Ok(mem_ops_tmp_buf.len())
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Ok(mem_ops_tmp_buf.len())
        );

        addrspace.protect(&mapped, ProtFlags::PROT_NONE).unwrap();
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );

        drop(addrspace);
        engine_thread.join().unwrap();
    }

    #[test]
    fn test_addr_space_give_upgrade_downgrade_take_access() {
        let (mut addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let engine_thread = thread::spawn(move || {
            engine.run(|_pagefault| Ok(())).unwrap();
        });

        addrspace.reserve_any(PAGE_SIZE.try_into().unwrap()).unwrap();
        let mapped = addrspace
            .map_anonymous_any(
                PAGE_SIZE.try_into().unwrap(),
                ProtFlags::PROT_READ.union(ProtFlags::PROT_WRITE),
                MapFlags::MAP_PRIVATE,
            )
            .unwrap();

        let mut mem_ops = NonFaultingMemOps::new().unwrap();
        let mut mem_ops_tmp_buf = [0u8];

        // Initially, page doesn't have access
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );

        addrspace.give_access(&mapped, SomePageAccess::ReadOnly, None).unwrap();
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Ok(mem_ops_tmp_buf.len())
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );

        addrspace.upgrade_access(&mapped).unwrap();
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Ok(mem_ops_tmp_buf.len())
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Ok(mem_ops_tmp_buf.len())
        );

        addrspace.take_access(&mapped).unwrap();
        assert_eq!(
            mem_ops.read(NonNull::from(mapped.start).as_ptr(), &mut mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );
        assert_eq!(
            mem_ops.write(NonNull::from(mapped.start).as_ptr(), &mem_ops_tmp_buf),
            Err(crate::interceptmem::mem_ops::NonFaultingMemOpsError::WouldFault)
        );

        drop(addrspace);
        engine_thread.join().unwrap();
    }

    #[test]
    fn test_addr_space_pagefaults() {
        let (addrspace, mut engine) = AddrSpace::new(true).unwrap();
        let addrspace = Arc::new(RwLock::new(addrspace));

        let reserved = addrspace
            .write()
            .unwrap()
            .reserve_any((2 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        let page_0_addr = reserved.start;
        let page_1_addr = reserved
            .start
            .enclosing_range(PAGE_SIZE.try_into().unwrap())
            .unwrap()
            .end;

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
                            assert_eq!(addr, page_0_addr);
                            assert_eq!(pagefault.access, SomePageAccess::ReadOnly);
                            let data: [u8; PAGE_SIZE] = [42; PAGE_SIZE];
                            addrspace
                                .write()
                                .unwrap()
                                .give_access(&range, SomePageAccess::ReadOnly, Some(&data))
                                .unwrap();
                        }
                        1 => {
                            assert_eq!(addr, page_0_addr);
                            assert_eq!(pagefault.access, SomePageAccess::ReadWrite);
                            addrspace.write().unwrap().upgrade_access(&range).unwrap();
                        }
                        2 => {
                            assert_eq!(addr, page_1_addr);
                            assert_eq!(pagefault.access, SomePageAccess::ReadOnly);
                            addrspace
                                .write()
                                .unwrap()
                                .take_access(&page_0_addr.enclosing_range(PAGE_SIZE.try_into().unwrap()).unwrap())
                                .unwrap();
                            let data: [u8; PAGE_SIZE] = [11; PAGE_SIZE];
                            addrspace
                                .write()
                                .unwrap()
                                .give_access(&range, SomePageAccess::ReadWrite, Some(&data))
                                .unwrap();
                        }
                        3 => {
                            assert_eq!(addr, page_0_addr);
                            assert_eq!(pagefault.access, SomePageAccess::ReadOnly);
                            addrspace
                                .write()
                                .unwrap()
                                .downgrade_access(&page_1_addr.enclosing_range(PAGE_SIZE.try_into().unwrap()).unwrap())
                                .unwrap();
                            let data: [u8; PAGE_SIZE] = [17; PAGE_SIZE];
                            addrspace
                                .write()
                                .unwrap()
                                .give_access(&range, SomePageAccess::ReadOnly, Some(&data))
                                .unwrap();
                        }
                        4 => {
                            assert_eq!(addr, page_1_addr);
                            assert_eq!(pagefault.access, SomePageAccess::ReadWrite);
                            addrspace.write().unwrap().upgrade_access(&range).unwrap();
                        }

                        _ => panic!("shouldn't have happened"),
                    }
                    Ok(())
                })
                .unwrap();
        });

        let mapped = addrspace
            .write()
            .unwrap()
            .map_anonymous_any(
                reserved.len(),
                ProtFlags::PROT_READ.union(ProtFlags::PROT_WRITE),
                MapFlags::MAP_PRIVATE,
            )
            .unwrap();
        assert_eq!(reserved, mapped);

        let page_0_ptr = NonNull::from(mapped.start).as_ptr() as *mut u8;
        let page_1_ptr = unsafe { page_0_ptr.add(PAGE_SIZE) };

        {
            let page_0_val = unsafe { *(page_0_ptr) }; // 1st pagefault - page_0 RO access
            // engine_thread gives RO access to page_0
            assert_eq!(page_0_val, 42);
        }
        {
            unsafe { *(page_0_ptr) = 13 }; // 2nd pagefault - page_0 RW access
            // engine_thread upgrades page_0 access to RW
        }
        {
            let page_1_val = unsafe { *(page_1_ptr) }; // 3rd pagefault - page_1 RO access
            // engine_thread takes access from page_0
            // engine_thread gives RW access to page_1
            assert_eq!(page_1_val, 11);
            unsafe { *(page_1_ptr) = 19 };
        }
        {
            let page_0_val = unsafe { *(page_0_ptr) }; // 4th pagefault - page_0 RO access
            // engine_thread downgrades page_1 access to RO
            // engine_thread gives RO access to page_0
            assert_eq!(page_0_val, 17);
        }
        {
            unsafe { *(page_1_ptr) = 7 }; // 5th pagefault - page_1 RW access
            // engine_thread upgrades page_1 access to RW
        }

        drop(addrspace);
        engine_thread.join().unwrap();
        assert_eq!(fault_counter.load(Ordering::Relaxed), 5);
    }
}
