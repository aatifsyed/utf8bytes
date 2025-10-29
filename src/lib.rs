extern crate alloc;

mod bytes;
mod bytes_mut;

use core::fmt;

pub use bytes::Utf8Bytes;
pub use bytes_mut::Utf8BytesMut;

#[derive(Debug, Clone, PartialEq)]
pub struct FromUtf8Error<T> {
    bytes: T,
    error: core::str::Utf8Error,
}

impl<T> FromUtf8Error<T> {
    pub fn inner(&self) -> &T {
        &self.bytes
    }
    pub fn into_inner(self) -> T {
        self.bytes
    }
    pub fn into_utf8_lossy(self) -> Utf8BytesMut
    where
        T: Into<Vec<u8>>,
    {
        let v = self.into_inner().into();
        match String::from_utf8_lossy(&v) {
            std::borrow::Cow::Borrowed(it) => it.into(), // TODO(two allocations)
            std::borrow::Cow::Owned(it) => it.into(),
        }
    }
    pub fn utf8_error(&self) -> core::str::Utf8Error {
        self.error
    }
}

impl<T> From<FromUtf8Error<T>> for core::str::Utf8Error {
    fn from(value: FromUtf8Error<T>) -> Self {
        value.error
    }
}

impl<T: fmt::Debug + Send + Sync + 'static> From<FromUtf8Error<T>> for std::io::Error {
    fn from(value: FromUtf8Error<T>) -> Self {
        std::io::Error::new(std::io::ErrorKind::InvalidData, value)
    }
}

impl<T: fmt::Debug> core::error::Error for FromUtf8Error<T> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.error.source()
    }
}

impl<T> fmt::Display for FromUtf8Error<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        self.error.fmt(f)
    }
}
