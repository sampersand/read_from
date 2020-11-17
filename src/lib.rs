#![deny(unsafe_code)]
/*!
The [`ReadFrom`] and [`WriteTo`] traits.

These traits allow you to represent the ability of a type to be serialized/
deserialized into an arbitrary byte stream. Because there's no universal way to
represent integers (outside of `u8` and `i8`), endian types are provided to
explicitly denote the endianness when deserializing.

//! This is _different_ from ser/de in that we don't have a self-described format,
//! but rather an arbitrary sequence of input bytes.
*/

use std::io::{self, Read, Write};
use std::mem::size_of;

/// Used to deserialize types from an input stream (i.e. a [`Read`]
/// implementation).
///
/// # Example
/// This implements [`ReadFrom`] for a simple `TinyRational` struct.
/// ```rust
/// use read_from::ReadFrom;
/// use std::io::{self, Cursor, Read};
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// pub struct TinyRational {
///    numer: i8,
///    denom: u8
/// }
/// 
/// #[derive(Debug)]
/// pub enum TinyRationalReadError {
///    DenomIsZero,
///    Io(io::Error)
/// }
///
/// impl ReadFrom for TinyRational {
///    type Error = TinyRationalReadError;
///
///    fn read_from<R: Read>(mut inp: R) -> Result<Self, Self::Error> {
///       let mut buf = [0; 2];
///       inp.read_exact(&mut buf).map_err(TinyRationalReadError::Io)?;
///       let numer = buf[0] as i8;
///       let denom = buf[1] as u8;
///       if denom == 0 {
///          Err(TinyRationalReadError::DenomIsZero)
///       } else {
///          Ok(Self { numer, denom })
///       }
///    }
/// }
///
/// assert_eq!(
///    TinyRational::read_from(Cursor::new(&[3, 4])).unwrap(),
///    TinyRational { numer: 3, denom: 4 });
/// assert!(matches!(
///    TinyRational::read_from(Cursor::new(&[3, 0])).unwrap_err(),
///    TinyRationalReadError::DenomIsZero
/// ));
/// ```
pub trait ReadFrom : Sized {
	/// What error can happen when trying to read?
	type Error;

	/// Attempts to construct `Self` from the given input stream.
	fn read_from<R: Read>(input: R) -> Result<Self, Self::Error>;
}

/// Used to serialize types into an output stream (i.e. a [`Write`]
/// implementation).
///
/// # Example
/// This implements [`WriteTo`] for a simple `TinyRational` struct.
/// ```rust
/// use read_from::WriteTo;
/// use std::io::{self, Write};
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// pub struct TinyRational {
///    numer: i8,
///    denom: u8
/// }
///
/// impl WriteTo for TinyRational {
///    type Error = io::Error;
///
///    fn write_to<W: Write>(&self, mut out: W) -> Result<usize, Self::Error> {
///       out.write_all(&[self.numer as u8, self.denom]).and(Ok(2))
///    }
/// }
///
/// let mut buf = Vec::new();
/// TinyRational { numer: 3, denom: 4 }.write_to(&mut buf).unwrap();
///
/// assert_eq!(buf, &[3, 4]);
/// ```
pub trait WriteTo {
	/// What error can happen when trying to write?
	type Error;

	/// Attempts to write `self` to the given output stream, returning the number
	/// of bytes written on success.
	fn write_to<W: Write>(&self, output: W) -> Result<usize, Self::Error>;
}

impl ReadFrom for u8 {
	type Error = io::Error;

	fn read_from<R: Read>(mut inp: R) -> io::Result<Self> {
		let mut buf = [0; 1];
		inp.read_exact(&mut buf)?;
		let [byte] = buf;
		Ok(byte)
	}
}

impl ReadFrom for i8 {
	type Error = io::Error;

	fn read_from<R: Read>(mut inp: R) -> io::Result<Self> {
		let mut buf = [0; 1];
		inp.read_exact(&mut buf)?;
		let [byte] = buf;
		Ok(byte as _)
	}
}

impl WriteTo for u8 {
	type Error = io::Error;

	fn write_to<W: Write>(&self, mut out: W) -> io::Result<usize> {
		out.write_all(&[*self]).and(Ok(1))
	}
}

impl WriteTo for i8 {
	type Error = io::Error;

	fn write_to<W: Write>(&self, mut out: W) -> io::Result<usize> {
		out.write_all(&[*self as u8]).and(Ok(1))
	}
}

/// A type that can be used to read/write integers in a little-endian format.
///
/// # Example
/// ```rust
/// use read_from::{WriteTo, ReadFrom, LittleEndian};
/// use std::io::Cursor;
///
/// let mut buf = vec![];
/// LittleEndian(0xaabbccdd_u32).write_to(&mut buf).unwrap();
/// assert_eq!(buf, [0xdd, 0xcc, 0xbb, 0xaa]);
///
/// let cursor = Cursor::new(&buf);
/// assert_eq!(0xaabbccdd_u32, LittleEndian::read_from(cursor).unwrap().0);
/// ```
#[repr(transparent)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LittleEndian<T>(pub T);

/// A type that can be used to deserialize integers in big-endian format.
/// 
/// # Example
/// ```rust
/// use read_from::{WriteTo, ReadFrom, BigEndian};
/// use std::io::Cursor;
///
/// let mut buf = vec![];
/// BigEndian(0xaabbccdd_u32).write_to(&mut buf).unwrap();
/// assert_eq!(buf, [0xaa, 0xbb, 0xcc, 0xdd]);
///
/// let cursor = Cursor::new(&buf);
/// assert_eq!(0xaabbccdd_u32, BigEndian::read_from(cursor).unwrap().0);
/// ```
#[repr(transparent)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BigEndian<T>(pub T);

/// A type that can be used to deserialize integers in native-endian format.
/// 
/// # Example
/// ```rust
/// use read_from::{WriteTo, ReadFrom, NativeEndian};
/// use std::io::Cursor;
///
/// let mut buf = vec![];
/// NativeEndian(0xaabbccdd_u32).write_to(&mut buf).unwrap();
///
/// if cfg!(target_endian="little") {
///    assert_eq!(buf, [0xdd, 0xcc, 0xbb, 0xaa]);
/// } else {
///    assert_eq!(buf, [0xaa, 0xbb, 0xcc, 0xdd]);
/// }
///
/// let cursor = Cursor::new(&buf);
/// assert_eq!(0xaabbccdd_u32, NativeEndian::read_from(cursor).unwrap().0);
/// ```
#[repr(transparent)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NativeEndian<T>(pub T);

/// Network endianness is big endianness.
pub type NetworkEndian<T> = BigEndian<T>;

macro_rules! impl_endian_traits {
	($endian:ident $from_bytes:ident $to_bytes:ident; $($ty:ident)*) => {
		$(
			impl ReadFrom for $endian<$ty> {
				type Error = io::Error;

				fn read_from<R: Read>(mut inp: R) -> Result<Self, Self::Error> {
					let mut buf = [0; size_of::<$ty>()];
					inp.read_exact(&mut buf)?;
					Ok(Self(<$ty>::$from_bytes(buf)))
				}
			}
		)*
		$(
			impl WriteTo for $endian<$ty> {
				type Error = io::Error;

				fn write_to<W: Write>(&self, mut out: W)
					-> Result<usize, Self::Error>
				{
					out.write_all(&self.0.$to_bytes()).and(Ok(size_of::<$ty>()))
				}
			}
		)*

	};
	($($ty:ident)*) => {
		impl_endian_traits!(LittleEndian from_le_bytes to_le_bytes; $($ty)*);
		impl_endian_traits!(BigEndian from_be_bytes to_be_bytes; $($ty)*);
		impl_endian_traits!(NativeEndian from_ne_bytes to_ne_bytes; $($ty)*);
	};
}

impl_endian_traits!(u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 f32 f64);
