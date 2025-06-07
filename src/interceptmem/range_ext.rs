use std::{
    cmp::{max, min},
    ops::Range,
};

use super::page_addr::PageAddr;

#[allow(dead_code)]
pub trait RangeExtOps {
    fn intersection(&self, other: &Self) -> Self;
    fn encloses(&self, other: &Self) -> bool;
}
impl RangeExtOps for Range<PageAddr> {
    fn intersection(&self, other: &Self) -> Self {
        let start = max(self.start, other.start);
        let end = min(self.end, other.end);
        if end <= start {
            // Return empty range starting from `self.start`
            self.start..self.start
        } else {
            start..end
        }
    }

    fn encloses(&self, other: &Self) -> bool {
        self.intersection(other) == *other
    }
}

#[cfg(test)]
mod tests {
    use std::{ffi::c_void, ptr::NonNull};

    use crate::interceptmem::page_addr::{PAGE_SIZE, RangeExtLen};

    use super::*;

    #[test]
    fn test_range_ext_ops_nonempty_intersection() {
        // (10*PAGE_SIZE)..(25*PAGE_SIZE) range
        let range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 10) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((15 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        // (20*PAGE_SIZE)..(45*PAGE_SIZE) range
        let intersecting_range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 20) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((25 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        let intersection = range.intersection(&intersecting_range);
        assert_eq!(intersection.len(), 5 * PAGE_SIZE);
        assert_eq!(
            intersection.start,
            PageAddr::try_from(NonNull::new((PAGE_SIZE * 20) as *mut c_void).unwrap()).unwrap()
        );
        assert_eq!(
            intersection.end,
            PageAddr::try_from(NonNull::new((PAGE_SIZE * 25) as *mut c_void).unwrap()).unwrap()
        );
    }

    #[test]
    fn test_range_ext_ops_empty_intersection() {
        // (10*PAGE_SIZE)..(25*PAGE_SIZE) range
        let range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 10) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((15 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        // (30*PAGE_SIZE)..(65*PAGE_SIZE) range
        let intersecting_range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 30) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((35 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        let intersection = range.intersection(&intersecting_range);
        assert!(intersection.is_empty());
        assert_eq!(intersection.start, range.start);
        assert_eq!(intersection.end, range.start);
    }

    #[test]
    fn test_range_ext_ops_encloses() {
        // (10*PAGE_SIZE)..(25*PAGE_SIZE) range
        let range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 10) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((20 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        // (20*PAGE_SIZE)..(45*PAGE_SIZE) range
        let other_range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 15) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((10 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        assert!(range.encloses(&other_range));
    }

    #[test]
    fn test_range_ext_ops_doesnt_enclose() {
        // (10*PAGE_SIZE)..(25*PAGE_SIZE) range
        let range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 10) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((20 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        // (30*PAGE_SIZE)..(65*PAGE_SIZE) range
        let other_range = PageAddr::try_from(NonNull::new((PAGE_SIZE * 15) as *mut c_void).unwrap())
            .unwrap()
            .enclosing_range((25 * PAGE_SIZE).try_into().unwrap())
            .unwrap();

        assert!(!range.encloses(&other_range));
    }
}
