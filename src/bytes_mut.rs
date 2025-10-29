use crate::FromUtf8Error;

use super::Utf8Bytes;

use core::iter::FromIterator;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};
use core::ptr::{self};
use core::{cmp, fmt, hash};

use alloc::{
    borrow::{Borrow, BorrowMut},
    string::String,
    vec::Vec,
};

/// A unique reference to a contiguous slice of memory.
///
/// `BytesMut` represents a unique view into a potentially shared memory region.
/// Given the uniqueness guarantee, owners of `BytesMut` handles are able to
/// mutate the memory.
///
/// `BytesMut` can be thought of as containing a `buf: Arc<Vec<u8>>`, an offset
/// into `buf`, a slice length, and a guarantee that no other `BytesMut` for the
/// same `buf` overlaps with its slice. That guarantee means that a write lock
/// is not required.
///
/// # Growth
///
/// `BytesMut`'s `BufMut` implementation will implicitly grow its buffer as
/// necessary. However, explicitly reserving the required space up-front before
/// a series of inserts will be more efficient.
///
/// # Examples
///
/// ```
/// use bytes::{BytesMut, BufMut};
///
/// let mut buf = BytesMut::with_capacity(64);
///
/// buf.put_u8(b'h');
/// buf.put_u8(b'e');
/// buf.put(&b"llo"[..]);
///
/// assert_eq!(&buf[..], b"hello");
///
/// // Freeze the buffer so that it can be shared
/// let a = buf.freeze();
///
/// // This does not allocate, instead `b` points to the same memory.
/// let b = a.clone();
///
/// assert_eq!(&a[..], b"hello");
/// assert_eq!(&b[..], b"hello");
/// ```
pub struct Utf8BytesMut {
    inner: bytes::BytesMut,
}

impl Utf8BytesMut {
    pub fn from_bytes_mut(bytes: bytes::BytesMut) -> Result<Self, FromUtf8Error<bytes::BytesMut>> {
        match str::from_utf8(&bytes) {
            Ok(_) => Ok(unsafe { Self::from_bytes_mut_unchecked(bytes) }),
            Err(error) => Err(FromUtf8Error { bytes, error }),
        }
    }
    pub const unsafe fn from_bytes_mut_unchecked(inner: bytes::BytesMut) -> Self {
        Self { inner }
    }
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(&self.inner) }
    }
    pub fn as_mut_str(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(&mut self.inner) }
    }
}

impl Utf8BytesMut {
    /// Creates a new `BytesMut` with the specified capacity.
    ///
    /// The returned `BytesMut` will be able to hold at least `capacity` bytes
    /// without reallocating.
    ///
    /// It is important to note that this function does not specify the length
    /// of the returned `BytesMut`, but only the capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::{BytesMut, BufMut};
    ///
    /// let mut bytes = BytesMut::with_capacity(64);
    ///
    /// // `bytes` contains no data, even though there is capacity
    /// assert_eq!(bytes.len(), 0);
    ///
    /// bytes.put(&b"hello world"[..]);
    ///
    /// assert_eq!(&bytes[..], b"hello world");
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Utf8BytesMut {
        unsafe { Self::from_bytes_mut_unchecked(bytes::BytesMut::with_capacity(capacity)) }
    }

    /// Creates a new `BytesMut` with default capacity.
    ///
    /// Resulting object has length 0 and unspecified capacity.
    /// This function does not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::{BytesMut, BufMut};
    ///
    /// let mut bytes = BytesMut::new();
    ///
    /// assert_eq!(0, bytes.len());
    ///
    /// bytes.reserve(2);
    /// bytes.put_slice(b"xy");
    ///
    /// assert_eq!(&b"xy"[..], &bytes[..]);
    /// ```
    #[inline]
    pub fn new() -> Utf8BytesMut {
        Utf8BytesMut::with_capacity(0)
    }

    /// Returns the number of bytes contained in this `BytesMut`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let b = BytesMut::from(&b"hello"[..]);
    /// assert_eq!(b.len(), 5);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the `BytesMut` has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let b = BytesMut::with_capacity(64);
    /// assert!(b.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the number of bytes the `BytesMut` can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let b = BytesMut::with_capacity(64);
    /// assert_eq!(b.capacity(), 64);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Converts `self` into an immutable `Bytes`.
    ///
    /// The conversion is zero cost and is used to indicate that the slice
    /// referenced by the handle will no longer be mutated. Once the conversion
    /// is done, the handle can be cloned and shared across threads.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::{BytesMut, BufMut};
    /// use std::thread;
    ///
    /// let mut b = BytesMut::with_capacity(64);
    /// b.put(&b"hello world"[..]);
    /// let b1 = b.freeze();
    /// let b2 = b1.clone();
    ///
    /// let th = thread::spawn(move || {
    ///     assert_eq!(&b1[..], b"hello world");
    /// });
    ///
    /// assert_eq!(&b2[..], b"hello world");
    /// th.join().unwrap();
    /// ```
    #[inline]
    pub fn freeze(self) -> Utf8Bytes {
        unsafe { Utf8Bytes::from_bytes_unchecked(self.inner.freeze()) }
    }

    /// Creates a new `BytesMut` containing `len` zeros.
    ///
    /// The resulting object has a length of `len` and a capacity greater
    /// than or equal to `len`. The entire length of the object will be filled
    /// with zeros.
    ///
    /// On some platforms or allocators this function may be faster than
    /// a manual implementation.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let zeros = BytesMut::zeroed(42);
    ///
    /// assert!(zeros.capacity() >= 42);
    /// assert_eq!(zeros.len(), 42);
    /// zeros.into_iter().for_each(|x| assert_eq!(x, 0));
    /// ```
    pub fn zeroed(len: usize) -> Utf8BytesMut {
        unsafe { Self::from_bytes_mut_unchecked(bytes::BytesMut::zeroed(len)) }
    }

    /// Splits the bytes into two at the given index.
    ///
    /// Afterwards `self` contains elements `[0, at)`, and the returned
    /// `BytesMut` contains elements `[at, capacity)`. It's guaranteed that the
    /// memory does not move, that is, the address of `self` does not change,
    /// and the address of the returned slice is `at` bytes after that.
    ///
    /// This is an `O(1)` operation that just increases the reference count
    /// and sets a few indices.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut a = BytesMut::from(&b"hello world"[..]);
    /// let mut b = a.split_off(5);
    ///
    /// a[0] = b'j';
    /// b[0] = b'!';
    ///
    /// assert_eq!(&a[..], b"jello");
    /// assert_eq!(&b[..], b"!world");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > capacity`.
    #[must_use = "consider BytesMut::truncate if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> Utf8BytesMut {
        let _char_boundary = self.as_str().split_at(at);
        unsafe { Self::from_bytes_mut_unchecked(self.inner.split_off(at)) }
    }

    /// Removes the bytes from the current view, returning them in a new
    /// `BytesMut` handle.
    ///
    /// Afterwards, `self` will be empty, but will retain any additional
    /// capacity that it had before the operation. This is identical to
    /// `self.split_to(self.len())`.
    ///
    /// This is an `O(1)` operation that just increases the reference count and
    /// sets a few indices.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::{BytesMut, BufMut};
    ///
    /// let mut buf = BytesMut::with_capacity(1024);
    /// buf.put(&b"hello world"[..]);
    ///
    /// let other = buf.split();
    ///
    /// assert!(buf.is_empty());
    /// assert_eq!(1013, buf.capacity());
    ///
    /// assert_eq!(other, b"hello world"[..]);
    /// ```
    #[must_use = "consider BytesMut::clear if you don't need the other half"]
    pub fn split(&mut self) -> Utf8BytesMut {
        unsafe { Self::from_bytes_mut_unchecked(self.inner.split()) }
    }

    /// Splits the buffer into two at the given index.
    ///
    /// Afterwards `self` contains elements `[at, len)`, and the returned `BytesMut`
    /// contains elements `[0, at)`.
    ///
    /// This is an `O(1)` operation that just increases the reference count and
    /// sets a few indices.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut a = BytesMut::from(&b"hello world"[..]);
    /// let mut b = a.split_to(5);
    ///
    /// a[0] = b'!';
    /// b[0] = b'j';
    ///
    /// assert_eq!(&a[..], b"!world");
    /// assert_eq!(&b[..], b"jello");
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    #[must_use = "consider BytesMut::advance if you don't need the other half"]
    pub fn split_to(&mut self, at: usize) -> Utf8BytesMut {
        let _char_boundary = self.as_str().split_at(at);
        unsafe { Self::from_bytes_mut_unchecked(self.inner.split_to(at)) }
    }

    /// Shortens the buffer, keeping the first `len` bytes and dropping the
    /// rest.
    ///
    /// If `len` is greater than the buffer's current length, this has no
    /// effect.
    ///
    /// Existing underlying capacity is preserved.
    ///
    /// The [split_off](`Self::split_off()`) method can emulate `truncate`, but this causes the
    /// excess bytes to be returned instead of dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut buf = BytesMut::from(&b"hello world"[..]);
    /// buf.truncate(5);
    /// assert_eq!(buf, b"hello"[..]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        fn floor_char_boundary(s: &str, index: usize) -> usize {
            if index >= s.len() {
                s.len()
            } else {
                let lower_bound = index.saturating_sub(3);
                let new_index = s.as_bytes()[lower_bound..=index]
                    .iter()
                    .rposition(|b| is_utf8_char_boundary(*b));

                // SAFETY: we know that the character boundary will be within four bytes
                unsafe { lower_bound + new_index.unwrap_unchecked() }
            }
        }

        fn is_utf8_char_boundary(b: u8) -> bool {
            // This is bit magic equivalent to: b < 128 || b >= 192
            (b as i8) >= -0x40
        }
        self.inner.truncate(floor_char_boundary(self.as_str(), len));
    }

    /// Clears the buffer, removing all data. Existing capacity is preserved.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut buf = BytesMut::from(&b"hello world"[..]);
    /// buf.clear();
    /// assert!(buf.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Resizes the buffer so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the buffer is extended by the
    /// difference with each additional byte set to `value`. If `new_len` is
    /// less than `len`, the buffer is simply truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut buf = BytesMut::new();
    ///
    /// buf.resize(3, 0x1);
    /// assert_eq!(&buf[..], &[0x1, 0x1, 0x1]);
    ///
    /// buf.resize(2, 0x2);
    /// assert_eq!(&buf[..], &[0x1, 0x1]);
    ///
    /// buf.resize(4, 0x3);
    /// assert_eq!(&buf[..], &[0x1, 0x1, 0x3, 0x3]);
    /// ```
    pub fn resize(&mut self, new_len: usize, ch: u8) {
        assert!(ch.is_ascii());
        let additional = if let Some(additional) = new_len.checked_sub(self.len()) {
            additional
        } else {
            self.truncate(new_len);
            return;
        };

        if additional == 0 {
            return;
        }

        self.reserve(additional);
        let dst = self.spare_capacity_mut().as_mut_ptr();
        // SAFETY: `spare_capacity_mut` returns a valid, properly aligned pointer and we've
        // reserved enough space to write `additional` bytes.
        unsafe { ptr::write_bytes(dst, ch, additional) };

        // SAFETY: There are at least `new_len` initialized bytes in the buffer so no
        // uninitialized bytes are being exposed.
        unsafe { self.set_len(new_len) };
    }

    /// Sets the length of the buffer.
    ///
    /// This will explicitly set the size of the buffer without actually
    /// modifying the data, so it is up to the caller to ensure that the data
    /// has been initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut b = BytesMut::from(&b"hello world"[..]);
    ///
    /// unsafe {
    ///     b.set_len(5);
    /// }
    ///
    /// assert_eq!(&b[..], b"hello");
    ///
    /// unsafe {
    ///     b.set_len(11);
    /// }
    ///
    /// assert_eq!(&b[..], b"hello world");
    /// ```
    #[inline]
    pub unsafe fn set_len(&mut self, len: usize) {
        unsafe { self.inner.set_len(len) }
    }

    /// Reserves capacity for at least `additional` more bytes to be inserted
    /// into the given `BytesMut`.
    ///
    /// More than `additional` bytes may be reserved in order to avoid frequent
    /// reallocations. A call to `reserve` may result in an allocation.
    ///
    /// Before allocating new buffer space, the function will attempt to reclaim
    /// space in the existing buffer. If the current handle references a view
    /// into a larger original buffer, and all other handles referencing part
    /// of the same original buffer have been dropped, then the current view
    /// can be copied/shifted to the front of the buffer and the handle can take
    /// ownership of the full buffer, provided that the full buffer is large
    /// enough to fit the requested additional capacity.
    ///
    /// This optimization will only happen if shifting the data from the current
    /// view to the front of the buffer is not too expensive in terms of the
    /// (amortized) time required. The precise condition is subject to change;
    /// as of now, the length of the data being shifted needs to be at least as
    /// large as the distance that it's shifted by. If the current view is empty
    /// and the original buffer is large enough to fit the requested additional
    /// capacity, then reallocations will never happen.
    ///
    /// # Examples
    ///
    /// In the following example, a new buffer is allocated.
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut buf = BytesMut::from(&b"hello"[..]);
    /// buf.reserve(64);
    /// assert!(buf.capacity() >= 69);
    /// ```
    ///
    /// In the following example, the existing buffer is reclaimed.
    ///
    /// ```
    /// use bytes::{BytesMut, BufMut};
    ///
    /// let mut buf = BytesMut::with_capacity(128);
    /// buf.put(&[0; 64][..]);
    ///
    /// let ptr = buf.as_ptr();
    /// let other = buf.split();
    ///
    /// assert!(buf.is_empty());
    /// assert_eq!(buf.capacity(), 64);
    ///
    /// drop(other);
    /// buf.reserve(128);
    ///
    /// assert_eq!(buf.capacity(), 128);
    /// assert_eq!(buf.as_ptr(), ptr);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Attempts to cheaply reclaim already allocated capacity for at least `additional` more
    /// bytes to be inserted into the given `BytesMut` and returns `true` if it succeeded.
    ///
    /// `try_reclaim` behaves exactly like `reserve`, except that it never allocates new storage
    /// and returns a `bool` indicating whether it was successful in doing so:
    ///
    /// `try_reclaim` returns false under these conditions:
    ///  - The spare capacity left is less than `additional` bytes AND
    ///  - The existing allocation cannot be reclaimed cheaply or it was less than
    ///    `additional` bytes in size
    ///
    /// Reclaiming the allocation cheaply is possible if the `BytesMut` has no outstanding
    /// references through other `BytesMut`s or `Bytes` which point to the same underlying
    /// storage.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut buf = BytesMut::with_capacity(64);
    /// assert_eq!(true, buf.try_reclaim(64));
    /// assert_eq!(64, buf.capacity());
    ///
    /// buf.extend_from_slice(b"abcd");
    /// let mut split = buf.split();
    /// assert_eq!(60, buf.capacity());
    /// assert_eq!(4, split.capacity());
    /// assert_eq!(false, split.try_reclaim(64));
    /// assert_eq!(false, buf.try_reclaim(64));
    /// // The split buffer is filled with "abcd"
    /// assert_eq!(false, split.try_reclaim(4));
    /// // buf is empty and has capacity for 60 bytes
    /// assert_eq!(true, buf.try_reclaim(60));
    ///
    /// drop(buf);
    /// assert_eq!(false, split.try_reclaim(64));
    ///
    /// split.clear();
    /// assert_eq!(4, split.capacity());
    /// assert_eq!(true, split.try_reclaim(64));
    /// assert_eq!(64, split.capacity());
    /// ```
    // I tried splitting out try_reclaim_inner after the short circuits, but it was inlined
    // regardless with Rust 1.78.0 so probably not worth it
    #[inline]
    #[must_use = "consider BytesMut::reserve if you need an infallible reservation"]
    pub fn try_reclaim(&mut self, additional: usize) -> bool {
        self.inner.try_reclaim(additional)
    }

    /// Appends given bytes to this `BytesMut`.
    ///
    /// If this `BytesMut` object does not have enough capacity, it is resized
    /// first.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut buf = BytesMut::with_capacity(0);
    /// buf.extend_from_slice(b"aaabbb");
    /// buf.extend_from_slice(b"cccddd");
    ///
    /// assert_eq!(b"aaabbbcccddd", &buf[..]);
    /// ```
    #[inline]
    pub fn extend_from_str(&mut self, extend: &str) {
        self.inner.extend_from_slice(extend.as_bytes());
    }

    /// Absorbs a `BytesMut` that was previously split off.
    ///
    /// If the two `BytesMut` objects were previously contiguous and not mutated
    /// in a way that causes re-allocation i.e., if `other` was created by
    /// calling `split_off` on this `BytesMut`, then this is an `O(1)` operation
    /// that just decreases a reference count and sets a few indices.
    /// Otherwise this method degenerates to
    /// `self.extend_from_slice(other.as_ref())`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// let mut buf = BytesMut::with_capacity(64);
    /// buf.extend_from_slice(b"aaabbbcccddd");
    ///
    /// let split = buf.split_off(6);
    /// assert_eq!(b"aaabbb", &buf[..]);
    /// assert_eq!(b"cccddd", &split[..]);
    ///
    /// buf.unsplit(split);
    /// assert_eq!(b"aaabbbcccddd", &buf[..]);
    /// ```
    pub fn unsplit(&mut self, other: Utf8BytesMut) {
        self.inner.unsplit(other.inner);
    }

    /// Returns the remaining spare capacity of the buffer as a slice of `MaybeUninit<u8>`.
    ///
    /// The returned slice can be used to fill the buffer with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// [`set_len`] method.
    ///
    /// [`set_len`]: BytesMut::set_len
    ///
    /// # Examples
    ///
    /// ```
    /// use bytes::BytesMut;
    ///
    /// // Allocate buffer big enough for 10 bytes.
    /// let mut buf = BytesMut::with_capacity(10);
    ///
    /// // Fill in the first 3 elements.
    /// let uninit = buf.spare_capacity_mut();
    /// uninit[0].write(0);
    /// uninit[1].write(1);
    /// uninit[2].write(2);
    ///
    /// // Mark the first 3 bytes of the buffer as being initialized.
    /// unsafe {
    ///     buf.set_len(3);
    /// }
    ///
    /// assert_eq!(&buf[..], &[0, 1, 2]);
    /// ```
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.inner.spare_capacity_mut()
    }
}

impl AsRef<[u8]> for Utf8BytesMut {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

impl AsRef<str> for Utf8BytesMut {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Deref for Utf8BytesMut {
    type Target = str;

    #[inline]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl AsMut<str> for Utf8BytesMut {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl DerefMut for Utf8BytesMut {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<'a> From<&'a str> for Utf8BytesMut {
    fn from(src: &'a str) -> Utf8BytesMut {
        unsafe { Self::from_bytes_mut_unchecked(src.as_bytes().into()) }
    }
}

impl From<Utf8BytesMut> for Utf8Bytes {
    fn from(src: Utf8BytesMut) -> Utf8Bytes {
        src.freeze()
    }
}

impl From<Utf8BytesMut> for bytes::BytesMut {
    fn from(src: Utf8BytesMut) -> bytes::BytesMut {
        src.inner
    }
}

impl<T: AsRef<str>> PartialEq<T> for Utf8BytesMut {
    fn eq(&self, other: &T) -> bool {
        self.as_str().eq(other.as_ref())
    }
}

impl Eq for Utf8BytesMut {}

impl<T: AsRef<str>> PartialOrd<T> for Utf8BytesMut {
    fn partial_cmp(&self, other: &T) -> Option<cmp::Ordering> {
        self.as_str().partial_cmp(other.as_ref())
    }
}

impl Ord for Utf8BytesMut {
    fn cmp(&self, other: &Utf8BytesMut) -> cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl Default for Utf8BytesMut {
    #[inline]
    fn default() -> Utf8BytesMut {
        Utf8BytesMut::new()
    }
}

impl hash::Hash for Utf8BytesMut {
    fn hash<H>(&self, state: &mut H)
    where
        H: hash::Hasher,
    {
        self.as_str().hash(state);
    }
}

impl Borrow<str> for Utf8BytesMut {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl BorrowMut<str> for Utf8BytesMut {
    fn borrow_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl fmt::Write for Utf8BytesMut {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.inner.write_str(s)
    }

    #[inline]
    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        self.inner.write_fmt(args)
    }
}

impl Clone for Utf8BytesMut {
    fn clone(&self) -> Utf8BytesMut {
        Utf8BytesMut::from(&self[..])
    }
}

impl Extend<char> for Utf8BytesMut {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = char>,
    {
        let iter = iter.into_iter();

        let (lower, _) = iter.size_hint();
        self.reserve(lower);

        for c in iter {
            fmt::Write::write_char(self, c).unwrap()
        }
    }
}

impl<'a> Extend<&'a char> for Utf8BytesMut {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = &'a char>,
    {
        self.extend(iter.into_iter().copied())
    }
}

impl Extend<Utf8Bytes> for Utf8BytesMut {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = Utf8Bytes>,
    {
        for bytes in iter {
            self.extend_from_str(&bytes)
        }
    }
}

impl FromIterator<char> for Utf8BytesMut {
    fn from_iter<T: IntoIterator<Item = char>>(into_iter: T) -> Self {
        unsafe {
            Self::from_bytes_mut_unchecked(
                String::from_iter(into_iter)
                    .into_bytes()
                    .into_iter()
                    .collect(),
            )
        }
    }
}

impl<'a> FromIterator<&'a char> for Utf8BytesMut {
    fn from_iter<T: IntoIterator<Item = &'a char>>(into_iter: T) -> Self {
        Self::from_iter(into_iter.into_iter().copied())
    }
}

/*
 *
 * ===== PartialEq / PartialOrd =====
 *
 */

impl PartialEq<[u8]> for Utf8BytesMut {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_str().as_bytes() == other
    }
}

impl PartialOrd<[u8]> for Utf8BytesMut {
    fn partial_cmp(&self, other: &[u8]) -> Option<cmp::Ordering> {
        self.as_str().as_bytes().partial_cmp(other)
    }
}

impl PartialEq<Utf8BytesMut> for [u8] {
    fn eq(&self, other: &Utf8BytesMut) -> bool {
        *other == *self
    }
}

impl PartialOrd<Utf8BytesMut> for [u8] {
    fn partial_cmp(&self, other: &Utf8BytesMut) -> Option<cmp::Ordering> {
        <[u8] as PartialOrd<[u8]>>::partial_cmp(self, other.as_bytes())
    }
}

impl PartialEq<str> for Utf8BytesMut {
    fn eq(&self, other: &str) -> bool {
        &**self == other
    }
}

impl PartialOrd<str> for Utf8BytesMut {
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        (**self).partial_cmp(other)
    }
}

impl PartialEq<Utf8BytesMut> for str {
    fn eq(&self, other: &Utf8BytesMut) -> bool {
        *other == *self
    }
}

impl PartialOrd<Utf8BytesMut> for str {
    fn partial_cmp(&self, other: &Utf8BytesMut) -> Option<cmp::Ordering> {
        <str as PartialOrd<str>>::partial_cmp(self, other)
    }
}

impl PartialEq<Utf8BytesMut> for Vec<u8> {
    fn eq(&self, other: &Utf8BytesMut) -> bool {
        self == other.as_bytes()
    }
}

impl PartialEq<Utf8BytesMut> for String {
    fn eq(&self, other: &Utf8BytesMut) -> bool {
        *other == *self
    }
}

impl PartialOrd<Utf8BytesMut> for String {
    fn partial_cmp(&self, other: &Utf8BytesMut) -> Option<cmp::Ordering> {
        <str as PartialOrd<str>>::partial_cmp(self, other)
    }
}

impl PartialEq<Utf8BytesMut> for &[u8] {
    fn eq(&self, other: &Utf8BytesMut) -> bool {
        *self == other.as_bytes()
    }
}

impl PartialOrd<Utf8BytesMut> for &[u8] {
    fn partial_cmp(&self, other: &Utf8BytesMut) -> Option<cmp::Ordering> {
        <[u8] as PartialOrd<[u8]>>::partial_cmp(self, other.as_bytes())
    }
}

impl PartialEq<Utf8BytesMut> for &str {
    fn eq(&self, other: &Utf8BytesMut) -> bool {
        *self == other.as_str()
    }
}

impl PartialOrd<Utf8BytesMut> for &str {
    fn partial_cmp(&self, other: &Utf8BytesMut) -> Option<cmp::Ordering> {
        other.partial_cmp(self)
    }
}

impl PartialEq<Utf8BytesMut> for bytes::Bytes {
    fn eq(&self, other: &Utf8BytesMut) -> bool {
        self == other.as_bytes()
    }
}

impl From<Utf8BytesMut> for Vec<u8> {
    fn from(value: Utf8BytesMut) -> Self {
        value.inner.into()
    }
}

impl From<Utf8BytesMut> for String {
    fn from(bytes: Utf8BytesMut) -> Self {
        unsafe { Self::from_utf8_unchecked(Vec::from(bytes.inner)) }
    }
}

impl From<String> for Utf8BytesMut {
    fn from(value: String) -> Self {
        unsafe { Self::from_bytes_mut_unchecked(value.into_bytes().into_iter().collect()) }
    }
}
