use super::Utf8BytesMut;

use core::iter::FromIterator;
use core::ops::{Deref, RangeBounds};
use core::{cmp, hash};
use std::borrow::Cow;

use alloc::{borrow::Borrow, boxed::Box, string::String, vec::Vec};

/// A cheaply cloneable and sliceable chunk of contiguous memory.
///
/// `Bytes` is an efficient container for storing and operating on contiguous
/// slices of memory. It is intended for use primarily in networking code, but
/// could have applications elsewhere as well.
///
/// `Bytes` values facilitate zero-copy network programming by allowing multiple
/// `Bytes` objects to point to the same underlying memory.
///
/// `Bytes` does not have a single implementation. It is an interface, whose
/// exact behavior is implemented through dynamic dispatch in several underlying
/// implementations of `Bytes`.
///
/// All `Bytes` implementations must fulfill the following requirements:
/// - They are cheaply cloneable and thereby shareable between an unlimited amount
///   of components, for example by modifying a reference count.
/// - Instances can be sliced to refer to a subset of the original buffer.
///
/// ```
/// use bytes::Bytes;
///
/// let mut mem = Bytes::from("Hello world");
/// let a = mem.slice(0..5);
///
/// assert_eq!(a, "Hello");
///
/// let b = mem.split_to(6);
///
/// assert_eq!(mem, "world");
/// assert_eq!(b, "Hello ");
/// ```
///
/// # Memory layout
///
/// The `Bytes` struct itself is fairly small, limited to 4 `usize` fields used
/// to track information about which segment of the underlying memory the
/// `Bytes` handle has access to.
///
/// `Bytes` keeps both a pointer to the shared state containing the full memory
/// slice and a pointer to the start of the region visible by the handle.
/// `Bytes` also tracks the length of its view into the memory.
///
/// # Sharing
///
/// `Bytes` contains a vtable, which allows implementations of `Bytes` to define
/// how sharing/cloning is implemented in detail.
/// When `Bytes::clone()` is called, `Bytes` will call the vtable function for
/// cloning the backing storage in order to share it behind multiple `Bytes`
/// instances.
///
/// For `Bytes` implementations which refer to constant memory (e.g. created
/// via `Bytes::from_static()`) the cloning implementation will be a no-op.
///
/// For `Bytes` implementations which point to a reference counted shared storage
/// (e.g. an `Arc<[u8]>`), sharing will be implemented by increasing the
/// reference count.
///
/// Due to this mechanism, multiple `Bytes` instances may point to the same
/// shared memory region.
/// Each `Bytes` instance can point to different sections within that
/// memory region, and `Bytes` instances may or may not have overlapping views
/// into the memory.
///
/// The following diagram visualizes a scenario where 2 `Bytes` instances make
/// use of an `Arc`-based backing storage, and provide access to different views:
///
/// ```text
///
///    Arc ptrs                   ┌─────────┐
///    ________________________ / │ Bytes 2 │
///   /                           └─────────┘
///  /          ┌───────────┐     |         |
/// |_________/ │  Bytes 1  │     |         |
/// |           └───────────┘     |         |
/// |           |           | ___/ data     | tail
/// |      data |      tail |/              |
/// v           v           v               v
/// ┌─────┬─────┬───────────┬───────────────┬─────┐
/// │ Arc │     │           │               │     │
/// └─────┴─────┴───────────┴───────────────┴─────┘
/// ```
pub struct Utf8Bytes {
    inner: bytes::Bytes,
}

impl Utf8Bytes {
    pub const unsafe fn from_bytes_unchecked(inner: bytes::Bytes) -> Self {
        Self { inner }
    }
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.inner) }
    }
}

impl Utf8Bytes {
    /// Creates a new empty `Bytes`.
    ///
    /// This will not allocate and the returned `Bytes` handle will be empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let b = Bytes::new();
    /// assert_eq!(&b[..], b"");
    /// ```
    #[inline]
    pub const fn new() -> Self {
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::new()) }
    }

    /// Creates a new `Bytes` from a static slice.
    ///
    /// The returned `Bytes` will point directly to the static slice. There is
    /// no allocating or copying.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let b = Bytes::from_static(b"hello");
    /// assert_eq!(&b[..], b"hello");
    /// ```
    #[inline]
    pub const fn from_static(bytes: &'static str) -> Self {
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::from_static(bytes.as_bytes())) }
    }

    /// Create [Bytes] with a buffer whose lifetime is controlled
    /// via an explicit owner.
    ///
    /// A common use case is to zero-copy construct from mapped memory.
    ///
    /// ```
    /// # struct File;
    /// #
    /// # impl File {
    /// #     pub fn open(_: &str) -> Result<Self, ()> {
    /// #         Ok(Self)
    /// #     }
    /// # }
    /// #
    /// # mod memmap2 {
    /// #     pub struct Mmap;
    /// #
    /// #     impl Mmap {
    /// #         pub unsafe fn map(_file: &super::File) -> Result<Self, ()> {
    /// #             Ok(Self)
    /// #         }
    /// #     }
    /// #
    /// #     impl AsRef<[u8]> for Mmap {
    /// #         fn as_ref(&self) -> &[u8] {
    /// #             b"buf"
    /// #         }
    /// #     }
    /// # }
    /// use bytes::Bytes;
    /// use memmap2::Mmap;
    ///
    /// # fn main() -> Result<(), ()> {
    /// let file = File::open("upload_bundle.tar.gz")?;
    /// let mmap = unsafe { Mmap::map(&file) }?;
    /// let b = Bytes::from_owner(mmap);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// The `owner` will be transferred to the constructed [Bytes] object, which
    /// will ensure it is dropped once all remaining clones of the constructed
    /// object are dropped. The owner will then be responsible for dropping the
    /// specified region of memory as part of its [Drop] implementation.
    ///
    /// Note that converting [Bytes] constructed from an owner into a [BytesMut]
    /// will always create a deep copy of the buffer into newly allocated memory.
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
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::from_owner(AsBytes(owner))) }
    }

    /// Returns the number of bytes contained in this `Bytes`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let b = Bytes::from(&b"hello"[..]);
    /// assert_eq!(b.len(), 5);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the `Bytes` has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let b = Bytes::new();
    /// assert!(b.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns true if this is the only reference to the data and
    /// `Into<BytesMut>` would avoid cloning the underlying buffer.
    ///
    /// Always returns false if the data is backed by a [static slice](Bytes::from_static),
    /// or an [owner](Bytes::from_owner).
    ///
    /// The result of this method may be invalidated immediately if another
    /// thread clones this value while this is being called. Ensure you have
    /// unique access to this value (`&mut Bytes`) first if you need to be
    /// certain the result is valid (i.e. for safety reasons).
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let a = Bytes::from(vec![1, 2, 3]);
    /// assert!(a.is_unique());
    /// let b = a.clone();
    /// assert!(!a.is_unique());
    /// ```
    pub fn is_unique(&self) -> bool {
        self.inner.is_unique()
    }

    /// Creates `Bytes` instance from slice, by copying it.
    pub fn copy_from_str(data: &str) -> Self {
        unsafe { Self::from_bytes_unchecked(bytes::Bytes::copy_from_slice(data.as_bytes())) }
    }

    /// Returns a slice of self for the provided range.
    ///
    /// This will increment the reference count for the underlying memory and
    /// return a new `Bytes` handle set to the slice.
    ///
    /// This operation is `O(1)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let a = Bytes::from(&b"hello world"[..]);
    /// let b = a.slice(2..5);
    ///
    /// assert_eq!(&b[..], b"llo");
    /// ```
    ///
    /// # Panics
    ///
    /// Requires that `begin <= end` and `end <= self.len()`, otherwise slicing
    /// will panic.
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        let lo = range.start_bound().cloned();
        let hi = range.end_bound().cloned();
        self.as_str().get((lo, hi)).unwrap();
        unsafe { Self::from_bytes_unchecked(self.inner.slice((lo, hi))) }
    }

    /// Returns a slice of self that is equivalent to the given `subset`.
    ///
    /// When processing a `Bytes` buffer with other tools, one often gets a
    /// `&[u8]` which is in fact a slice of the `Bytes`, i.e. a subset of it.
    /// This function turns that `&[u8]` into another `Bytes`, as if one had
    /// called `self.slice()` with the offsets that correspond to `subset`.
    ///
    /// This operation is `O(1)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let bytes = Bytes::from(&b"012345678"[..]);
    /// let as_slice = bytes.as_ref();
    /// let subset = &as_slice[2..6];
    /// let subslice = bytes.slice_ref(&subset);
    /// assert_eq!(&subslice[..], b"2345");
    /// ```
    ///
    /// # Panics
    ///
    /// Requires that the given `sub` slice is in fact contained within the
    /// `Bytes` buffer; otherwise this function will panic.
    pub fn slice_ref(&self, subset: &str) -> Self {
        unsafe { Self::from_bytes_unchecked(self.inner.slice_ref(subset.as_bytes())) }
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
    /// use bytes::Bytes;
    ///
    /// let mut a = Bytes::from(&b"hello world"[..]);
    /// let b = a.split_off(5);
    ///
    /// assert_eq!(&a[..], b"hello");
    /// assert_eq!(&b[..], b" world");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    #[must_use = "consider Bytes::truncate if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> Self {
        let _char_boundary = self.as_str().split_at(at);
        unsafe { Self::from_bytes_unchecked(self.inner.split_off(at)) }
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
    /// use bytes::Bytes;
    ///
    /// let mut a = Bytes::from(&b"hello world"[..]);
    /// let b = a.split_to(5);
    ///
    /// assert_eq!(&a[..], b" world");
    /// assert_eq!(&b[..], b"hello");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    #[must_use = "consider Bytes::advance if you don't need the other half"]
    pub fn split_to(&mut self, at: usize) -> Self {
        let _char_boundary = self.as_str().split_at(at);
        unsafe { Self::from_bytes_unchecked(self.inner.split_to(at)) }
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
    /// use bytes::Bytes;
    ///
    /// let mut buf = Bytes::from(&b"hello world"[..]);
    /// buf.truncate(5);
    /// assert_eq!(buf, b"hello"[..]);
    /// ```
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        if len < self.len() {
            let _char_boundary = self.as_str().split_at(len);
            self.inner.truncate(len)
        };
    }

    /// Clears the buffer, removing all data.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::Bytes;
    ///
    /// let mut buf = Bytes::from(&b"hello world"[..]);
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
    /// use bytes::{Bytes, BytesMut};
    ///
    /// let bytes = Bytes::from(b"hello".to_vec());
    /// assert_eq!(bytes.try_into_mut(), Ok(BytesMut::from(&b"hello"[..])));
    /// ```
    pub fn try_into_mut(self) -> Result<Utf8BytesMut, Utf8Bytes> {
        if self.is_unique() {
            Ok(self.into())
        } else {
            Err(self)
        }
    }
}

impl Clone for Utf8Bytes {
    #[inline]
    fn clone(&self) -> Utf8Bytes {
        unsafe { Self::from_bytes_unchecked(self.inner.clone()) }
    }
    fn clone_from(&mut self, source: &Self) {
        self.inner.clone_from(&source.inner);
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
        (&**self).partial_cmp(other.as_str())
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
    /// Convert self into `BytesMut`.
    ///
    /// If `bytes` is unique for the entire original buffer, this will return a
    /// `BytesMut` with the contents of `bytes` without copying.
    /// If `bytes` is not unique for the entire original buffer, this will make
    /// a copy of `bytes` subset of the original buffer in a new `BytesMut`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::{Bytes, BytesMut};
    ///
    /// let bytes = Bytes::from(b"hello".to_vec());
    /// assert_eq!(BytesMut::from(bytes), BytesMut::from(&b"hello"[..]));
    /// ```
    fn from(utf8: Utf8Bytes) -> Self {
        utf8.inner
    }
}

impl From<Utf8Bytes> for Utf8BytesMut {
    /// Convert self into `BytesMut`.
    ///
    /// If `bytes` is unique for the entire original buffer, this will return a
    /// `BytesMut` with the contents of `bytes` without copying.
    /// If `bytes` is not unique for the entire original buffer, this will make
    /// a copy of `bytes` subset of the original buffer in a new `BytesMut`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::{Bytes, BytesMut};
    ///
    /// let bytes = Bytes::from(b"hello".to_vec());
    /// assert_eq!(BytesMut::from(bytes), BytesMut::from(&b"hello"[..]));
    /// ```
    fn from(bytes: Utf8Bytes) -> Self {
        todo!()
    }
}

impl From<String> for Utf8Bytes {
    fn from(s: String) -> Utf8Bytes {
        unsafe { Utf8Bytes::from_bytes_unchecked(bytes::Bytes::from(s.into_bytes())) }
    }
}

impl From<Utf8Bytes> for Vec<u8> {
    fn from(utf8: Utf8Bytes) -> Vec<u8> {
        utf8.inner.into()
    }
}
