use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};

use crate::{interceptmem::page_addr::PageAddr, nonempty_range::NonEmptyRange};

#[derive(Debug, Serialize, Deserialize, Encode, Decode)]
pub enum Request {
    Ping(usize),
    Reserve(NonEmptyRange<PageAddr>),
}

#[derive(Debug, Serialize, Deserialize, Encode, Decode)]
pub enum Response {
    Ping(usize),
    Reserve(Result<(), ()>),
}
