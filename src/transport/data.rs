use bincode::{Decode, Encode};
use nix::{
    libc::c_int,
    sys::mman::{MapFlags, ProtFlags},
};
use serde::{Deserialize, Serialize};

use crate::{interceptmem::page_addr::PageAddr, nonempty_range::NonEmptyRange};

#[derive(Debug, Serialize, Deserialize, Encode, Decode)]
pub enum Request {
    Ping(usize),
    Reserve(NonEmptyRange<PageAddr>),
    Map(NonEmptyRange<PageAddr>, ProtFlagsWrapper, MapFlagsWrapper),
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, Encode, Decode)]
pub struct ProtFlagsWrapper(c_int);
impl From<ProtFlags> for ProtFlagsWrapper {
    fn from(value: ProtFlags) -> Self {
        Self(value.bits())
    }
}
impl From<ProtFlagsWrapper> for ProtFlags {
    fn from(value: ProtFlagsWrapper) -> Self {
        ProtFlags::from_bits_truncate(value.0)
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, Encode, Decode)]
pub struct MapFlagsWrapper(c_int);
impl From<MapFlags> for MapFlagsWrapper {
    fn from(value: MapFlags) -> Self {
        Self(value.bits())
    }
}
impl From<MapFlagsWrapper> for MapFlags {
    fn from(value: MapFlagsWrapper) -> Self {
        MapFlags::from_bits_retain(value.0)
    }
}

#[derive(Debug, Serialize, Deserialize, Encode, Decode)]
pub enum Response {
    Ping(usize),
    Reserve(Result<(), ()>),
    Map(Result<(), ()>),
}
