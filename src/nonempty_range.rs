use std::{
    borrow::Borrow,
    ops::{Deref, Range},
};

use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonEmptyRange<T>(Range<T>);

#[derive(Debug, Error, Clone)]
pub enum NonEmptyRangeError {
    #[error("Empty range")]
    EmptyRange,
}

impl<T: PartialOrd> TryFrom<Range<T>> for NonEmptyRange<T> {
    type Error = NonEmptyRangeError;

    fn try_from(value: Range<T>) -> Result<Self, Self::Error> {
        if value.is_empty() {
            return Err(NonEmptyRangeError::EmptyRange);
        }
        Ok(Self(value))
    }
}
impl<T> From<NonEmptyRange<T>> for Range<T> {
    fn from(value: NonEmptyRange<T>) -> Self {
        value.0
    }
}
impl<T> Deref for NonEmptyRange<T> {
    type Target = Range<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T> Borrow<Range<T>> for &NonEmptyRange<T> {
    fn borrow(&self) -> &Range<T> {
        &self.0
    }
}
