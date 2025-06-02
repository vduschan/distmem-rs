use std::{
    ffi::c_void,
    os::fd::OwnedFd,
    slice::{from_raw_parts, from_raw_parts_mut},
};

use nix::{
    errno::Errno,
    libc::off_t,
    sys::memfd::{MFdFlags, memfd_create},
    unistd::{Whence, ftruncate, lseek, read, write},
};
use thiserror::Error;

#[allow(dead_code)]
#[derive(Debug)]
pub struct NonFaultingMemOps {
    memfd: OwnedFd,
    len: usize,
}

#[allow(dead_code)]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum NonFaultingMemOpsError {
    #[error("Runtime error ({errno}): {msg}")]
    RuntimeError { msg: String, errno: Errno },

    #[error("Operation would cause page fault")]
    WouldFault,
}

impl NonFaultingMemOps {
    #[allow(dead_code)]
    pub fn new() -> Result<Self, NonFaultingMemOpsError> {
        let memfd = memfd_create("NonFaultingMemOps", MFdFlags::MFD_CLOEXEC).map_err(|errno| {
            NonFaultingMemOpsError::RuntimeError {
                msg: "memfd creation failed".into(),
                errno,
            }
        })?;
        ftruncate(&memfd, 1).map_err(|errno| NonFaultingMemOpsError::RuntimeError {
            msg: "ftruncating memfd failed".into(),
            errno,
        })?;
        Ok(NonFaultingMemOps { memfd, len: 1 })
    }

    fn rewind_memfd(&mut self) -> Result<(), NonFaultingMemOpsError> {
        lseek(&self.memfd, 0, Whence::SeekSet).map_err(|errno| NonFaultingMemOpsError::RuntimeError {
            msg: "failed rewinding the memfd".into(),
            errno,
        })?;
        Ok(())
    }
    fn resize_memfd(&mut self, len: usize) -> Result<(), NonFaultingMemOpsError> {
        {
            let len = off_t::try_from(len).map_err(|_err| NonFaultingMemOpsError::RuntimeError {
                msg: "memfd len too large to ftruncate".into(),
                errno: Errno::UnknownErrno,
            })?;
            ftruncate(&self.memfd, len).map_err(|errno| NonFaultingMemOpsError::RuntimeError {
                msg: "ftruncating memfd failed".into(),
                errno,
            })?;
        }
        self.len = len;
        Ok(())
    }

    /// Reads memory pointed by `addr` into `out_buf` without causing a fault.
    ///
    /// # Returns
    ///
    /// Returns a number of bytes read, otherwise returns an error.
    ///
    /// If reading from `addr` to the `out_buf` would have caused a fault,
    /// `NonFaultingMemOpsError::WouldFault` error is returned.
    #[allow(dead_code)]
    pub fn read(&mut self, addr: *const c_void, out_buf: &mut [u8]) -> Result<usize, NonFaultingMemOpsError> {
        if out_buf.len() > self.len {
            self.resize_memfd(out_buf.len())?;
        }

        // Write into memfd causes a read from `addr`.
        // If read from `addr` would fault, write to memfd returns `EFAULT`.
        let in_buf = unsafe { from_raw_parts(addr as *const u8, out_buf.len()) };
        self.rewind_memfd()?;
        let write_count = match write(&self.memfd, in_buf) {
            Ok(write_count) => write_count,
            Err(Errno::EFAULT) => return Err(NonFaultingMemOpsError::WouldFault),
            Err(errno) => {
                return Err(NonFaultingMemOpsError::RuntimeError {
                    msg: "failed writing into memfd".into(),
                    errno,
                });
            }
        };

        let out_buf = &mut out_buf[..write_count];
        self.rewind_memfd()?;
        match read(&self.memfd, out_buf) {
            Ok(read_count) => Ok(read_count),
            Err(errno) => Err(NonFaultingMemOpsError::RuntimeError {
                msg: "reading from memfd failed".into(),
                errno,
            }),
        }
    }

    /// Writes `in_buf` to memory pointed by `addr` without causing a fault.
    ///
    /// # Returns
    ///
    /// Returns a number of bytes written, otherwise returns an error.
    ///
    /// If writing `in_buf` to  the `addr` memory would have caused a fault,
    /// `NonFaultingMemOpsError::WouldFault` error is returned.
    #[allow(dead_code)]
    pub fn write(&mut self, addr: *mut c_void, in_buf: &[u8]) -> Result<usize, NonFaultingMemOpsError> {
        if in_buf.len() > self.len {
            self.resize_memfd(in_buf.len())?;
        }

        self.rewind_memfd()?;
        let write_count = match write(&self.memfd, in_buf) {
            Ok(write_count) => write_count,
            Err(errno) => {
                return Err(NonFaultingMemOpsError::RuntimeError {
                    msg: "failed writing into memfd".into(),
                    errno,
                });
            }
        };

        // Read from memfd causes a write to `addr`.
        // If write to `addr` would fault, read from memfd returns `EFAULT`.
        let out_buf = unsafe { from_raw_parts_mut(addr as *mut u8, write_count) };
        self.rewind_memfd()?;
        match read(&self.memfd, out_buf) {
            Ok(read_count) => Ok(read_count),
            Err(Errno::EFAULT) => Err(NonFaultingMemOpsError::WouldFault),
            Err(errno) => Err(NonFaultingMemOpsError::RuntimeError {
                msg: "reading from memfd failed".into(),
                errno,
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use nix::sys::mman::{MapFlags, ProtFlags};

    use super::*;

    #[test]
    fn test_non_faulting_mem_ops() {
        let write_buf = [42u8];
        let mut read_buf = [0u8];

        let addr = unsafe {
            nix::sys::mman::mmap_anonymous(
                None,
                write_buf.len().try_into().unwrap(),
                ProtFlags::PROT_READ.union(ProtFlags::PROT_WRITE),
                MapFlags::MAP_PRIVATE,
            )
            .unwrap()
        };

        let mut mem_ops = NonFaultingMemOps::new().unwrap();

        {
            let write_count = mem_ops.write(addr.as_ptr(), &write_buf).unwrap();
            assert_eq!(write_count, write_buf.len());

            let read_count = mem_ops.read(addr.as_ptr(), &mut read_buf).unwrap();
            assert_eq!(read_count, 1);
            assert_eq!(read_buf, write_buf);
        }

        unsafe { nix::sys::mman::mprotect(addr, write_buf.len(), ProtFlags::PROT_READ).unwrap() };
        {
            let write_result = mem_ops.write(addr.as_ptr(), &write_buf);
            assert_eq!(write_result, Err(NonFaultingMemOpsError::WouldFault));

            let read_count = mem_ops.read(addr.as_ptr(), &mut read_buf).unwrap();
            assert_eq!(read_count, 1);
            assert_eq!(read_buf, write_buf);
        }

        unsafe { nix::sys::mman::mprotect(addr, write_buf.len(), ProtFlags::PROT_NONE).unwrap() };
        {
            let write_result = mem_ops.write(addr.as_ptr(), &write_buf);
            assert_eq!(write_result, Err(NonFaultingMemOpsError::WouldFault));

            let read_result = mem_ops.read(addr.as_ptr(), &mut read_buf);
            assert_eq!(read_result, Err(NonFaultingMemOpsError::WouldFault));
        }

        unsafe { nix::sys::mman::munmap(addr, 1).unwrap() };
    }
}
