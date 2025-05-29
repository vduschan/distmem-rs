/// This module provides primitives for mapping/unmapping memory pages which
/// access can be controlled and intercepted.
pub mod addr_space;
pub mod page_addr;
mod range_ext;
mod userfaultfd_ext;
