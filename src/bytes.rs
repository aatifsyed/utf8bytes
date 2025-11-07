use crate::FromUtf8Error;

use super::Utf8BytesMut;

use core::iter::FromIterator;
use core::ops::{Deref, RangeBounds};
use core::{cmp, fmt, hash};
use std::borrow::Cow;

use alloc::{borrow::Borrow, boxed::Box, string::String, vec::Vec};

/// A cheaply cloneable and sliceable chunk of contiguous memory filled with
/// UTF-8 bytes.
///
/// This is built on [`Bytes`](bytes::Bytes), see its documentation for more.
#[repr(transparent)]
pub struct Utf8Bytes {
    /// # Invariant
    /// - contains UTF-8.
    #[deprecated = "use the accessors to preserve the invariants"]
    inner: bytes::Bytes,
}

impl Utf8Bytes {
    /// Wrap `bytes` if it is UTF-8.
    ///
    /// If it is not, you can perform a lossy conversion using [`FromUtf8Error::into_utf8_lossy`].
    pub fn from_bytes(bytes: bytes::Bytes) -> Result<Self, FromUtf8Error<bytes::Bytes>> {
        match str::from_utf8(&bytes) {
            // SAFETY:
            // - performed validation
            Ok(_) => Ok(unsafe { Self::from_bytes_unchecked(bytes) }),
            Err(error) => Err(FromUtf8Error { bytes, error }),
        }
    }

    /// # Safety
    /// `bytes` must only contain UTF-8.
    pub const unsafe fn from_bytes_unchecked(bytes: bytes::Bytes) -> Self {
        #[expect(deprecated)]
        Self { inner: bytes }
    }

    /// Get the contents of the buffer.
    pub fn as_str(&self) -> &str {
        // SAFETY:
        // - cannot create Self from invalid UTF-8 without using `unsafe`
        unsafe { str::from_utf8_unchecked(self.inner()) }
    }
}

impl Utf8Bytes {
    /// Return a shared reference to the inner object.
    #[inline]
    pub const fn inner(&self) -> &bytes::Bytes {
        #[expect(deprecated)]
        &self.inner
    }

    /// Return an exclusive reference to the inner object.
    ///
    /// # Safety
    /// - The returned bytes must be returned containing UTF-8
    #[inline]
    pub const unsafe fn inner_mut(&mut self) -> &mut bytes::Bytes {
        #[expect(deprecated)]
        &mut self.inner
    }
    #[inline]
    pub fn into_inner(self) -> bytes::Bytes {
        #[expect(deprecated)]
        self.inner
    }
}

impl Utf8Bytes {
    /// Creates a new empty `Bytes`.
    ///
    /// This will not allocate and the returned handle will be empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let b = Utf8Bytes::new();
    /// assert_eq!(b, "");
    /// ```
    #[inline]
    pub const fn new() -> Self {
        // SAFETY:
        // - empty is valid UTF-8
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::new()) }
    }

    /// Creates a new [`Utf8Bytes`] from a static slice.
    ///
    /// The returned [`Utf8Bytes`] will point directly to the static slice.
    /// There is no allocating or copying.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let b = Utf8Bytes::from_static("hello");
    /// assert_eq!(b, "hello");
    /// ```
    #[inline]
    pub const fn from_static(str: &'static str) -> Self {
        // SAFETY:
        // - bytes: &str
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::from_static(str.as_bytes())) }
    }

    /// Create [`Utf8Bytes`] with a buffer whose lifetime is controlled
    /// via an explicit owner.
    ///
    /// See [`bytes::Bytes::from_owner`] for more.
    pub fn from_owner<T>(owner: T) -> Self
    where
        T: AsRef<str> + Send + 'static,
    {
        #[repr(transparent)]
        struct AsBytes<T>(T);
        impl<T: AsRef<str>> AsRef<[u8]> for AsBytes<T> {
            fn as_ref(&self) -> &[u8] {
                self.0.as_ref().as_bytes()
            }
        }
        // SAFETY:
        // - owner: AsRef<str>
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::from_owner(AsBytes(owner))) }
    }

    /// Returns the number of bytes contained in this [`Utf8Bytes`].
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let b = Utf8Bytes::from("hello");
    /// assert_eq!(b.len(), 5);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.inner().len()
    }

    /// Returns true if the [`Utf8Bytes`] has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let b = Utf8Bytes::new();
    /// assert!(b.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.inner().is_empty()
    }

    /// Returns true if this is the only reference to the data and
    /// <code>[Into]<[Utf8BytesMut]></code> would avoid cloning the underlying
    /// buffer.
    ///
    /// Always returns false if the data is backed by a [static slice](Self::from_static),
    /// or an [owner](Self::from_owner).
    ///
    /// The result of this method may be invalidated immediately if another
    /// thread clones this value while this is being called. Ensure you have
    /// unique access to this value (`&mut Bytes`) first if you need to be
    /// certain the result is valid (i.e. for safety reasons).
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let a = Utf8Bytes::from(vec![1, 2, 3]);
    /// assert!(a.is_unique());
    /// let b = a.clone();
    /// assert!(!a.is_unique());
    /// ```
    pub fn is_unique(&self) -> bool {
        self.inner().is_unique()
    }

    /// Creates a [`Utf8Bytes`] instance from slice, by copying it.
    pub fn copy_from_str(data: &str) -> Self {
        // SAFETY:
        // - data: &str
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::copy_from_slice(data.as_bytes())) }
    }

    /// Returns a slice of self for the provided range.
    ///
    /// This will increment the reference count for the underlying memory and
    /// return a new [`Utf8Bytes`] handle set to the slice.
    ///
    /// This operation is `O(1)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let a = BytesMut::from("hello world");
    /// let b = a.slice(2..5);
    ///
    /// assert_eq!(b, "llo");
    /// ```
    ///
    /// # Panics
    ///
    /// - If `range` is out of bounds.
    /// - `range` breaks a char boundary.
    ///
    #[track_caller]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        let lo = range.start_bound().cloned();
        let hi = range.end_bound().cloned();
        self.as_str()
            .get((lo, hi))
            .expect("range out of bounds or not on a char boundary");
        // Safety:
        // - checked the equivalent operation on &str
        unsafe { Self::from_bytes_unchecked(self.inner().slice((lo, hi))) }
    }

    /// Returns a slice of self that is equivalent to the given `subset`.
    ///
    /// When processing a [`Utf8Bytes`] buffer with other tools, one often gets
    /// a `&str` which is in fact a slice of the [`Utf8Bytes`],
    /// i.e. a subset of it.
    ///
    /// This function turns that `&str` into another [`Utf8Bytes`],
    /// as if one had called `self.slice()` with the offsets that correspond to
    /// `subset`.
    ///
    /// This operation is `O(1)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let bytes = Utf8Bytes::from("012345678");
    /// let as_slice = bytes.as_ref();
    /// let subset = &as_slice[2..6];
    /// let subslice = bytes.slice_ref(&subset);
    /// assert_eq!(subslice, "2345");
    /// ```
    ///
    /// # Panics
    ///
    /// Requires that the given `subset` slice is in fact contained within the
    /// [`Utf8Bytes`] buffer; otherwise this function will panic.
    pub fn slice_ref(&self, subset: &str) -> Self {
        // SAFETY:
        // - subset: &str _and_ the forwarded call does the bounds checks
        unsafe { Self::from_bytes_unchecked(self.inner().slice_ref(subset.as_bytes())) }
    }

    /// Splits the bytes into two at the given index.
    ///
    /// Afterwards `self` contains elements `[0, at)`, and the returned `Bytes`
    /// contains elements `[at, len)`. It's guaranteed that the memory does not
    /// move, that is, the address of `self` does not change, and the address of
    /// the returned slice is `at` bytes after that.
    ///
    /// This is an `O(1)` operation that just increases the reference count and
    /// sets a few indices.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let mut a = Utf8Bytes::from("hello world");
    /// let b = a.split_off(5);
    ///
    /// assert_eq!(a, "hello");
    /// assert_eq!(b, " world");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > len` or does not lie on a char boundary.
    #[must_use = "consider Bytes::truncate if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> Self {
        let _char_boundary = self.as_str().split_at(at);
        // SAFETY:
        // - checked boundary above
        unsafe { Self::from_bytes_unchecked(self.inner_mut().split_off(at)) }
    }

    /// Splits the bytes into two at the given index.
    ///
    /// Afterwards `self` contains elements `[at, len)`, and the returned
    /// `Bytes` contains elements `[0, at)`.
    ///
    /// This is an `O(1)` operation that just increases the reference count and
    /// sets a few indices.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let mut a = Utf8Bytes::from("hello world");
    /// let b = a.split_to(5);
    ///
    /// assert_eq!(a, " world");
    /// assert_eq!(b, "hello");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > len` or does not lie on a char boundary.
    #[must_use = "consider Bytes::advance if you don't need the other half"]
    pub fn split_to(&mut self, at: usize) -> Self {
        let _char_boundary = self.as_str().split_at(at);
        // SAFETY:
        // - checked boundary above
        unsafe { Self::from_bytes_unchecked(self.inner_mut().split_to(at)) }
    }

    /// Shortens the buffer, keeping the first `len` bytes and dropping the
    /// rest.
    ///
    /// If `len` is greater than the buffer's current length, this has no
    /// effect.
    ///
    /// The [split_off](`Self::split_off()`) method can emulate `truncate`, but this causes the
    /// excess bytes to be returned instead of dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let mut buf = Utf8Bytes::from("hello world");
    /// buf.truncate(5);
    /// assert_eq!(buf, "hello");
    /// ```
    ///
    /// # Panics
    ///
    /// If `len` does not lie on a char boundary.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len < self.len() {
            let _char_boundary = self.as_str().split_at(len);
            // SAFETY:
            // - checked char boundary above
            unsafe { self.inner_mut().truncate(len) }
        };
    }

    /// Clears the buffer, removing all data.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::Utf8Bytes;
    ///
    /// let mut buf = Utf8Bytes::from("hello world");
    /// buf.clear();
    /// assert!(buf.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Try to convert self into `BytesMut`.
    ///
    /// If `self` is unique for the entire original buffer, this will succeed
    /// and return a `BytesMut` with the contents of `self` without copying.
    /// If `self` is not unique for the entire original buffer, this will fail
    /// and return self.
    ///
    /// This will also always fail if the buffer was constructed via either
    /// [from_owner](Bytes::from_owner) or [from_static](Bytes::from_static).
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::{Utf8Bytes, Utf8BytesMut};
    ///
    /// let bytes = Utf8Bytes::from("hello".to_string());
    /// assert_eq!(bytes.try_into_mut(), Ok(Utf8BytesMut::from("hello")));
    /// ```
    pub fn try_into_mut(self) -> Result<Utf8BytesMut, Utf8Bytes> {
        match self.into_inner().try_into_mut() {
            // SAFETY:
            // - the bytes came from `self`
            Ok(it) => Ok(unsafe { Utf8BytesMut::from_bytes_mut_unchecked(it) }),
            Err(it) => Err(unsafe { Self::from_bytes_unchecked(it) }),
        }
    }
}

impl fmt::Debug for Utf8Bytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl fmt::Display for Utf8Bytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl Clone for Utf8Bytes {
    #[inline]
    fn clone(&self) -> Utf8Bytes {
        unsafe { Self::from_bytes_unchecked(self.inner().clone()) }
    }
    fn clone_from(&mut self, source: &Self) {
        self.inner().clone_from(&source.inner());
    }
}

impl Deref for Utf8Bytes {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for Utf8Bytes {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for Utf8Bytes {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

impl hash::Hash for Utf8Bytes {
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        self.as_str().hash(state);
    }
}

impl Borrow<str> for Utf8Bytes {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl FromIterator<char> for Utf8Bytes {
    fn from_iter<T: IntoIterator<Item = char>>(into_iter: T) -> Self {
        String::from_iter(into_iter).into()
    }
}

// impl Eq

impl<T: AsRef<str>> PartialEq<T> for Utf8Bytes {
    fn eq(&self, other: &T) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl<T: AsRef<str>> PartialOrd<T> for Utf8Bytes {
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        self.as_str().partial_cmp(other.as_ref())
    }
}

impl Ord for Utf8Bytes {
    fn cmp(&self, other: &Utf8Bytes) -> cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl Eq for Utf8Bytes {}

impl PartialEq<Utf8Bytes> for str {
    fn eq(&self, other: &Utf8Bytes) -> bool {
        self.eq(other.as_str())
    }
}
impl PartialEq<Utf8Bytes> for String {
    fn eq(&self, other: &Utf8Bytes) -> bool {
        self.eq(other.as_str())
    }
}
impl<'a> PartialEq<Utf8Bytes> for Cow<'a, str> {
    fn eq(&self, other: &Utf8Bytes) -> bool {
        self.eq(other.as_str())
    }
}

impl PartialOrd<Utf8Bytes> for str {
    fn partial_cmp(&self, other: &Utf8Bytes) -> Option<cmp::Ordering> {
        self.partial_cmp(other.as_str())
    }
}
impl PartialOrd<Utf8Bytes> for String {
    fn partial_cmp(&self, other: &Utf8Bytes) -> Option<cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}
impl PartialOrd<Utf8Bytes> for Cow<'_, str> {
    fn partial_cmp(&self, other: &Utf8Bytes) -> Option<cmp::Ordering> {
        (**self).partial_cmp(other.as_str())
    }
}

// impl From

impl Default for Utf8Bytes {
    #[inline]
    fn default() -> Utf8Bytes {
        Utf8Bytes::new()
    }
}

impl From<&'static str> for Utf8Bytes {
    fn from(s: &'static str) -> Utf8Bytes {
        Utf8Bytes::from_static(s)
    }
}

impl From<Box<str>> for Utf8Bytes {
    fn from(slice: Box<str>) -> Utf8Bytes {
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::from(slice.into_boxed_bytes())) }
    }
}

impl From<Utf8Bytes> for bytes::Bytes {
    fn from(utf8: Utf8Bytes) -> Self {
        utf8.into_inner()
    }
}

impl From<Utf8Bytes> for Utf8BytesMut {
    /// Convert self into [`Utf8BytesMut`].
    ///
    /// If `bytes` is unique for the entire original buffer, this will return a
    /// `BytesMut` with the contents of `bytes` without copying.
    /// If `bytes` is not unique for the entire original buffer, this will make
    /// a copy of `bytes` subset of the original buffer in a new `BytesMut`.
    ///
    /// # Examples
    ///
    /// ```
    /// use utf8_bytes::{Utf8Bytes, Utf8BytesMut};
    ///
    /// let bytes = Utf8Bytes::from("hello".to_vec());
    /// assert_eq!(Utf8BytesMut::from(bytes), Utf8BytesMut::from("hello"));
    /// ```
    fn from(bytes: Utf8Bytes) -> Self {
        // SAFETY:
        // - `bytes` is preserved.
        unsafe { Self::from_bytes_mut_unchecked(bytes.into_inner().into()) }
    }
}

impl From<String> for Utf8Bytes {
    fn from(s: String) -> Utf8Bytes {
        // SAFETY:
        // - s contains UTF-8.
        unsafe { Utf8Bytes::from_bytes_unchecked(bytes::Bytes::from(s.into_bytes())) }
    }
}

impl From<Utf8Bytes> for Vec<u8> {
    fn from(utf8: Utf8Bytes) -> Vec<u8> {
        utf8.into_inner().into()
    }
}

impl From<Utf8Bytes> for String {
    fn from(utf8: Utf8Bytes) -> Self {
        // SAFETY:
        // - only contains UTF-8
        unsafe { String::from_utf8_unchecked(utf8.into()) }
    }
}
