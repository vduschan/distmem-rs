use std::os::fd::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, OwnedFd};

use linux_raw_sys::general::{_UFFDIO_API, UFFD_API, UFFD_USER_MODE_ONLY, UFFDIO, uffdio_api};
use nix::{
    errno::Errno,
    libc::{INT_MAX, INT_MIN, O_CLOEXEC, O_NONBLOCK, SYS_userfaultfd, c_int, c_long, syscall},
};

use userfaultfd as uffd;

fn syscall_userfaultfd(flags: c_int) -> Result<OwnedFd, Errno> {
    let fd = unsafe { syscall(SYS_userfaultfd, flags as c_long) };
    assert!(fd <= INT_MAX as c_long);
    assert!(fd >= INT_MIN as c_long);
    let fd = fd as c_int;
    if fd < 0 {
        let errno = -fd;
        return Err(Errno::from_raw(errno));
    }
    Ok(unsafe { OwnedFd::from_raw_fd(fd) })
}

nix::ioctl_readwrite!(ioctl_uffdio_api_raw, UFFDIO, _UFFDIO_API, uffdio_api);
unsafe fn ioctl_uffdio_api(
    fd: BorrowedFd,
    features: uffd::FeatureFlags,
) -> Result<uffd::IoctlFlags, Errno> {
    let mut arg = uffdio_api {
        api: UFFD_API as _,
        features: features.bits(),
        ioctls: 0,
    };
    let ret = unsafe { ioctl_uffdio_api_raw(fd.as_raw_fd(), &mut arg as *mut _) }?;
    assert_eq!(ret, 0);
    Ok(uffd::IoctlFlags::from_bits_retain(arg.ioctls))
}

pub struct UserfaultFdFlags {
    pub user_mode_only: bool,
    pub non_blocking: bool,
    pub close_on_exec: bool,
}
impl UserfaultFdFlags {
    fn as_raw(&self) -> c_int {
        let mut flags: c_int = 0;
        if self.user_mode_only {
            flags |= UFFD_USER_MODE_ONLY as c_int;
        }
        if self.non_blocking {
            flags |= O_NONBLOCK;
        }
        if self.close_on_exec {
            flags |= O_CLOEXEC;
        }
        flags
    }
}

pub fn userfaultfd_create(
    flags: UserfaultFdFlags,
    required_features: uffd::FeatureFlags,
    required_ioctls: uffd::IoctlFlags,
) -> Result<uffd::Uffd, Errno> {
    // If process doesn't have permission to open `/dev/userfaultfd`,
    // `UffdBuilder` would fail creating the `Uffd` instead of trying to create
    // it from the syscall.
    if let Ok(uffd) = uffd::UffdBuilder::new()
        .user_mode_only(flags.user_mode_only)
        .non_blocking(flags.non_blocking)
        .close_on_exec(flags.close_on_exec)
        .require_features(required_features)
        .require_ioctls(required_ioctls)
        .create()
    {
        return Ok(uffd);
    }

    // Retry from syscall.
    let fd = syscall_userfaultfd(flags.as_raw())?;
    let supported_ioctls = unsafe { ioctl_uffdio_api(fd.as_fd(), required_features) }?;
    if !supported_ioctls.contains(required_ioctls) {
        return Err(Errno::ENOTSUP);
    }
    Ok(unsafe { uffd::Uffd::from_raw_fd(fd.into_raw_fd()) })
}
