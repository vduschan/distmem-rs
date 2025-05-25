use std::num::NonZeroUsize;

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
