# `read_from`
The `ReadFrom` and `WriteTo` traits.

These traits allow you to represent the ability of a type to be serialized/
deserialized into an arbitrary byte stream. Because there's no universal way to
represent integers (outside of `u8` and `i8`), endian types are provided to
explicitly denote the endianness when deserializing.

//! This is _different_ from ser/de in that we don't have a self-described format,
//! but rather an arbitrary sequence of input bytes.
