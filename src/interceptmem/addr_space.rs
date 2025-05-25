use std::{num::NonZeroUsize, ops::Range};

use nix::{
    errno::Errno,
    sys::mman::{MapFlags, ProtFlags},
};
use thiserror::Error;

use super::page_addr::PageAddr;

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

#[allow(dead_code)]
pub struct AddrSpace();

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
        todo!()
    }

    /// Reserves a range of pages of the specified length for address space use.
    ///
    /// # Returns
    ///
    /// Returns a `Range<PageAddr>` representing the reserved range if successful,
    /// otherwise returns an error.
    #[allow(dead_code)]
    pub fn reserve_any(
        &mut self,
        _length: NonZeroUsize,
    ) -> Result<Range<PageAddr>, AddrSpaceError> {
        todo!()
    }

    /// Reserves the specified range of pages for address space use.
    ///
    /// # Returns
    ///
    /// Returns `Ok(())` if successful, otherwise returns an error.
    #[allow(dead_code)]
    pub fn reserve(&mut self, _range: Range<PageAddr>) -> Result<(), AddrSpaceError> {
        todo!()
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
