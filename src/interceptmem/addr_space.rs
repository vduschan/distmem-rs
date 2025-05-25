use std::{ffi::c_void, num::NonZeroUsize, ops::Range, ptr::NonNull};

use nix::{
    errno::Errno,
    sys::mman::{MapFlags, ProtFlags},
};
use rangemap::RangeMap;
use thiserror::Error;

use super::page_addr::{PageAddr, RangeExt};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum SomePageAccess {
    ReadOnly,
    ReadWrite,
}
#[allow(dead_code)]
pub type PageAccess = Option<SomePageAccess>;

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PageFault {
    addr: PageAddr,
    access: SomePageAccess,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PageState {
    access: PageAccess,
}

#[allow(dead_code)]
#[derive(Debug)]
pub struct AddrSpace {
    pages: RangeMap<PageAddr, Option<PageState>>,
}

#[allow(dead_code)]
#[derive(Debug, Error)]
pub enum AddrSpaceError {
    #[error("Invalid range: {msg}")]
    InvalidRange { msg: String },

    #[error("Generic runtime error ({errno}): {msg}")]
    RuntimeError { msg: String, errno: Errno },
}

impl AddrSpace {
    #[allow(dead_code)]
    pub fn new() -> (AddrSpace, AddrSpaceFaultReceiver) {
        (
            AddrSpace {
                pages: Default::default(),
            },
            AddrSpaceFaultReceiver(),
        )
    }

    /// Reserves a range of pages of the specified length for address space use.
    ///
    /// # Returns
    ///
    /// Returns a `Range<PageAddr>` representing the reserved range if successful,
    /// otherwise returns an error.
    #[allow(dead_code)]
    pub fn reserve_any(&mut self, length: NonZeroUsize) -> Result<Range<PageAddr>, AddrSpaceError> {
        let mmapped = unsafe {
            nix::sys::mman::mmap_anonymous(
                None,
                length,
                ProtFlags::PROT_NONE,
                MapFlags::MAP_PRIVATE,
            )
        }
        .map_err(|errno| AddrSpaceError::RuntimeError {
            msg: format!("mmap with len {} failed", length),
            errno,
        })?;
        let mmapped = unsafe { util::MmapGuard::from_raw(mmapped, length) };

        let reserved = PageAddr::try_from(mmapped.addr())
            .expect("`mmap_anonymous` should've returned a page address");
        let reserved = reserved.enclosing_range(mmapped.length()).expect(
            "`mmap_anonymous` should've returned pages that can be represented by the `PageAddr`",
        );

        assert!(!self.pages.overlaps(&reserved));
        self.pages.insert(reserved.clone(), None);
        mmapped.consume();
        Ok(reserved)
    }

    /// Reserves the specified range of pages for address space use.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn reserve(&mut self, range: Range<PageAddr>) -> Result<(), AddrSpaceError> {
        if self.pages.overlaps(&range) {
            return Err(AddrSpaceError::InvalidRange {
                msg: "part of the range already reserved".into(),
            });
        }

        let addr: NonNull<c_void> = range.start.into();
        let addr: NonZeroUsize = (addr.as_ptr() as usize)
            .try_into()
            .expect("non-null ptr is non-0");
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
            msg: "mmap failed".into(),
            errno,
        })?;
        let mmapped = unsafe { util::MmapGuard::from_raw(mmapped, length) };

        let reserved = PageAddr::try_from(mmapped.addr())
            .expect("`mmap_anonymous` should've returned a page address");
        let reserved = reserved.enclosing_range(mmapped.length()).expect(
            "`mmap_anonymous` should've returned pages that can be represented by the `PageAddr`",
        );

        self.pages.insert(reserved, None);
        mmapped.consume();
        Ok(())
    }

    /// Releases a previously reserved range of pages from address space.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn release(&mut self, _range: Range<PageAddr>) -> Result<(), AddrSpaceError> {
        todo!()
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
        _length: NonZeroUsize,
        _prot: ProtFlags,
        _flags: MapFlags,
    ) -> Result<Range<PageAddr>, AddrSpaceError> {
        todo!()
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
        _range: Range<PageAddr>,
        _prot: ProtFlags,
        _flags: MapFlags,
    ) -> Result<(), AddrSpaceError> {
        todo!()
    }

    /// Unmaps a previously mapped range of pages.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn unmap(&mut self, _range: Range<PageAddr>) -> Result<(), AddrSpaceError> {
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
        _range: Range<PageAddr>,
        _access: SomePageAccess,
        _data: Option<&[u8]>,
    ) -> Result<(), AddrSpaceError> {
        todo!();
    }

    /// Updates access to a previously mapped range of pages that has some access.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn update_access(
        &mut self,
        _range: Range<PageAddr>,
        _access: SomePageAccess,
    ) -> Result<(), AddrSpaceError> {
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
    pub fn take_access(&mut self, _range: Range<PageAddr>) -> Result<(), AddrSpaceError> {
        todo!();
    }
}

#[allow(dead_code)]
pub struct AddrSpaceFaultReceiver();

#[allow(dead_code)]
#[derive(Debug, Error)]
pub enum AddrSpaceFaultReceiverError {
    #[error("Generic runtime error ({errno}): {msg}")]
    RuntimeError { msg: String, errno: Errno },
}

impl AddrSpaceFaultReceiver {
    #[allow(dead_code)]
    pub fn recv(&self) -> Result<PageFault, AddrSpaceFaultReceiver> {
        todo!()
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
            self.0
                .expect("invariant: inner data is `Some` until `consume`d")
                .0
        }
        pub fn length(&self) -> NonZeroUsize {
            self.0
                .expect("invariant: inner data is `Some` until `consume`d")
                .1
        }
        pub fn consume(mut self) -> (NonNull<c_void>, NonZeroUsize) {
            self.0
                .take()
                .expect("invariant: inner data is `Some` until `consume`d")
        }
    }
    impl Drop for MmapGuard {
        fn drop(&mut self) {
            if let Some((addr, length)) = self.0 {
                unsafe { nix::sys::mman::munmap(addr, length.get()).unwrap() };
            }
        }
    }
}

impl Drop for AddrSpace {
    fn drop(&mut self) {
        for (range, state) in self.pages.iter() {
            if let Some(_state) = state {
                todo!();
            } else {
                unsafe {
                    nix::sys::mman::munmap(range.start.into(), range.len().get())
                        .expect("`munmap` should've succeeded on reserved range");
                };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interceptmem::{addr_space::util::MmapGuard, page_addr::PAGE_SIZE};

    use super::*;

    #[test]
    fn test_addr_space_reserve_any() {
        let (mut addrspace, _fault_receiver) = AddrSpace::new();
        let reserved = addrspace.reserve_any(1.try_into().unwrap()).unwrap();
        assert_eq!(reserved.len().get(), PAGE_SIZE);

        let inner_reserved = addrspace.pages.get_key_value(&reserved.start).unwrap();
        assert_eq!(*inner_reserved.0, reserved);
        assert_eq!(*inner_reserved.1, None);
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

        let (mut addrspace, _fault_receiver) = AddrSpace::new();

        // AddrSpace shouldn't reserve externally mmapped range
        let result = addrspace.reserve(occupied.clone());
        assert!(result.is_err());
    }
}
