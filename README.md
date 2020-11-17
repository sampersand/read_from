# `read-from`
The `ReadFrom` and `WriteTo` traits.

These traits allow you to represent the ability of a type to be serialized/
deserialized into an arbitrary byte stream. Because there's no universal way to
represent integers (outside of `u8` and `i8`), endian types are provided to
explicitly denote the endianness when deserializing.

# Serde
This is not the same as [serde](https://docs.serde.rs/serde/)! Serde is used to
serialize/deserialize types regardless of the data format. The `ReadFrom`/
`WriteTo` traits are intended to be used at a lower-level, where details such
as the ordering of bytes is important.
