use std::{ffi::c_void, num::NonZeroUsize, ops::Range, ptr::NonNull};

use thiserror::Error;

#[allow(dead_code)]
pub const PAGE_BITS: usize = 12;
#[allow(dead_code)]
pub const PAGE_SIZE: usize = 1 << PAGE_BITS;
#[allow(dead_code)]
pub const PAGE_MASK: usize = !(PAGE_SIZE - 1);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PageAddr(NonZeroUsize);

impl std::fmt::Debug for PageAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:01$x}", self.0, size_of_val(&self.0))
    }
}

impl std::fmt::Display for PageAddr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Delegate to Debug
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Error)]
pub enum PageAddrError {
    #[error("Invalid pointer: {msg}")]
    InvalidPointer { msg: String },
}

impl TryFrom<NonNull<c_void>> for PageAddr {
    type Error = PageAddrError;

    fn try_from(value: NonNull<c_void>) -> Result<Self, Self::Error> {
        let addr = NonZeroUsize::new(value.as_ptr() as usize).expect("non-null ptr is non-0");
        if addr.get() & !PAGE_MASK != 0 {
            return Err(PageAddrError::InvalidPointer {
                msg: "pointer is not page aligned".into(),
            });
        }
        Ok(PageAddr(addr))
    }
}

impl From<PageAddr> for NonNull<c_void> {
    fn from(value: PageAddr) -> Self {
        NonNull::new(value.0.get() as *mut c_void).expect("non-0 usize is non-null ptr")
    }
}

impl PageAddr {
    pub fn containing_page(value: NonNull<c_void>) -> Option<PageAddr> {
        let addr = (value.as_ptr() as usize) & PAGE_MASK;
        Some(PageAddr(NonZeroUsize::new(addr)?))
    }
    pub fn enclosing_range(self, length: NonZeroUsize) -> Option<Range<PageAddr>> {
        let end_addr = self.0.checked_add(length.get())?;
        let end_page_addr = end_addr.saturating_add(PAGE_SIZE - 1).get() & PAGE_MASK;
        Some(self..PageAddr(NonZeroUsize::new(end_page_addr).expect("end page should be > 0")))
    }
}

#[allow(dead_code)]
pub trait RangeExtLen {
    fn len(&self) -> NonZeroUsize;
}

impl RangeExtLen for Range<PageAddr> {
    fn len(&self) -> NonZeroUsize {
        let length = self
            .end
            .0
            .get()
            .checked_sub(self.start.0.get())
            .expect("invariant: start page should be < than end page");
        NonZeroUsize::new(length).expect("invariant: start page should be < than end page")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_try_from_nonnull() {
        let ptr = NonNull::new((42 * PAGE_SIZE) as *mut c_void).unwrap();
        let addr = PageAddr::try_from(ptr).unwrap();
        assert_eq!(addr.0, NonZeroUsize::new(42 * PAGE_SIZE).unwrap());

        let ptr_not_page_aligned = NonNull::new((42 * PAGE_SIZE + 1) as *mut c_void).unwrap();
        assert!(PageAddr::try_from(ptr_not_page_aligned).is_err());
    }

    #[test]
    fn test_from_page_addr_to_nonnull() {
        let addr = PageAddr(NonZeroUsize::new(42 * PAGE_SIZE).unwrap());
        let ptr: NonNull<c_void> = addr.into();
        assert_eq!(ptr.as_ptr() as usize, 42 * PAGE_SIZE);
    }

    #[test]
    fn test_containing_page() {
        let ptr_not_page_aligned = NonNull::new((42 * PAGE_SIZE + 1) as *mut c_void).unwrap();
        let addr = PageAddr::containing_page(ptr_not_page_aligned).unwrap();
        assert_eq!(addr.0, NonZeroUsize::new(42 * PAGE_SIZE).unwrap());

        let ptr_null_page = NonNull::new(1 as *mut c_void).unwrap();
        assert!(PageAddr::containing_page(ptr_null_page).is_none());
    }

    #[test]
    fn test_enclosing_range() {
        let addr: PageAddr = PageAddr(NonZeroUsize::new(42 * PAGE_SIZE).unwrap());
        let length = NonZeroUsize::new(PAGE_SIZE + 1).unwrap();
        let range = addr.enclosing_range(length).unwrap();
        assert_eq!(range.start, addr);
        assert_eq!(range.end, PageAddr(NonZeroUsize::new(44 * PAGE_SIZE).unwrap()));
    }

    #[test]
    fn test_range_ext_len() {
        let start = PageAddr(NonZeroUsize::new(42 * PAGE_SIZE).unwrap());
        let end = PageAddr(NonZeroUsize::new(44 * PAGE_SIZE).unwrap());
        let range = start..end;
        assert_eq!(range.len(), NonZeroUsize::new(2 * PAGE_SIZE).unwrap());
    }
}
