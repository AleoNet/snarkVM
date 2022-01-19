// Copyright (C) 2019-2021 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use crate::{
    error,
    fmt,
    io::{Read, Result as IoResult, Write},
    marker::PhantomData,
    Vec,
};
use serde::{
    de::{self, SeqAccess, Visitor},
    ser::{self, SerializeTuple},
    Deserializer,
    Serializer,
};

/// Takes as input a sequence of structs, and converts them to a series of little-endian bytes.
/// All traits that implement `ToBytes` can be automatically converted to bytes in this manner.
#[macro_export]
macro_rules! to_bytes_le {
    ($($x:expr),*) => ({
        let mut buffer = $crate::vec![];
        {$crate::push_bytes_to_vec!(buffer, $($x),*)}.map(|_| buffer)
    });
}

#[macro_export]
macro_rules! push_bytes_to_vec {
    ($buffer:expr, $y:expr, $($x:expr),*) => ({
        {ToBytes::write_le(&$y, &mut $buffer)}.and({$crate::push_bytes_to_vec!($buffer, $($x),*)})
    });

    ($buffer:expr, $x:expr) => ({
        ToBytes::write_le(&$x, &mut $buffer)
    })
}

pub trait ToBytes {
    /// Writes `self` into `writer` as little-endian bytes.
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()>
    where
        Self: Sized;

    /// Returns `self` as a byte array in little-endian order.
    fn to_bytes_le(&self) -> anyhow::Result<Vec<u8>>
    where
        Self: Sized,
    {
        Ok(to_bytes_le![self]?)
    }
}

pub trait FromBytes {
    /// Reads `Self` from `reader` as little-endian bytes.
    fn read_le<R: Read>(reader: R) -> IoResult<Self>
    where
        Self: Sized;

    /// Returns `Self` from a byte array in little-endian order.
    fn from_bytes_le(bytes: &[u8]) -> anyhow::Result<Self>
    where
        Self: Sized,
    {
        Ok(Self::read_le(bytes)?)
    }
}

pub struct ToBytesSerializer<T: ToBytes>(String, Option<usize>, PhantomData<T>);

impl<T: ToBytes> ToBytesSerializer<T> {
    ///
    /// Serializes a static-sized object as a byte array (without length encoding).
    ///
    pub fn serialize<S: Serializer>(object: &T, serializer: S) -> Result<S::Ok, S::Error> {
        let bytes = object.to_bytes_le().map_err(ser::Error::custom)?;
        let mut tuple = serializer.serialize_tuple(bytes.len())?;
        for byte in &bytes {
            tuple.serialize_element(byte)?;
        }
        tuple.end()
    }

    ///
    /// Serializes a dynamically-sized object as a byte array with length encoding.
    ///
    pub fn serialize_with_size_encoding<S: Serializer>(object: &T, serializer: S) -> Result<S::Ok, S::Error> {
        let bytes = object.to_bytes_le().map_err(ser::Error::custom)?;
        serializer.serialize_bytes(&bytes)
    }
}

pub struct FromBytesDeserializer<T: FromBytes>(String, Option<usize>, PhantomData<T>);

impl<'de, T: FromBytes> FromBytesDeserializer<T> {
    ///
    /// Deserializes a static-sized byte array (without length encoding).
    ///
    /// This method fails if `deserializer` is given an insufficient `size`.
    ///
    pub fn deserialize<D: Deserializer<'de>>(deserializer: D, name: &str, size: usize) -> Result<T, D::Error> {
        let mut buffer = Vec::with_capacity(size);
        deserializer.deserialize_tuple(size, FromBytesVisitor::new(&mut buffer, name))?;
        FromBytes::read_le(&buffer[..]).map_err(de::Error::custom)
    }

    ///
    /// Deserializes a dynamically-sized byte array.
    ///
    pub fn deserialize_with_size_encoding<D: Deserializer<'de>>(deserializer: D, name: &str) -> Result<T, D::Error> {
        let mut buffer = Vec::with_capacity(32);
        deserializer.deserialize_bytes(FromBytesVisitor::new(&mut buffer, name))?;
        FromBytes::read_le(&buffer[..]).map_err(de::Error::custom)
    }

    ///
    /// Attempts to deserialize a byte array (without length encoding).
    ///
    /// This method does *not* fail if `deserializer` is given an insufficient `size`,
    /// however this method fails if `FromBytes` fails to read the value of `T`.
    ///
    pub fn deserialize_extended<D: Deserializer<'de>>(
        deserializer: D,
        name: &str,
        size_a: usize,
        size_b: usize,
    ) -> Result<T, D::Error> {
        // Order the given sizes from smallest to largest.
        let (size_a, size_b) = match size_a < size_b {
            true => (size_a, size_b),
            false => (size_b, size_a),
        };

        // Reserve a new `Vec` with the larger size capacity.
        let mut buffer = Vec::with_capacity(size_b);

        // Attempt to deserialize on the larger size, to load up to the maximum buffer size.
        match deserializer.deserialize_tuple(size_b, FromBytesVisitor::new(&mut buffer, name)) {
            // Deserialized a full buffer, attempt to read up to `size_b`.
            Ok(()) => FromBytes::read_le(&buffer[..size_b]).map_err(de::Error::custom),
            // Deserialized a partial buffer, attempt to read up to `size_a`, if exactly `size_a` was read.
            Err(error) => match buffer.len() == size_a {
                true => FromBytes::read_le(&buffer[..size_a]).map_err(de::Error::custom),
                false => Err(error),
            },
        }
    }
}

pub struct FromBytesVisitor<'a>(&'a mut Vec<u8>, String, Option<usize>);

impl<'a, 'de> FromBytesVisitor<'a> {
    pub fn new(buffer: &'a mut Vec<u8>, name: &str) -> Self {
        Self(buffer, name.to_string(), None)
    }
}

impl<'a, 'de> Visitor<'de> for FromBytesVisitor<'a> {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(&format!("a valid {} ", self.1))
    }

    fn visit_borrowed_bytes<E: serde::de::Error>(self, bytes: &'de [u8]) -> Result<Self::Value, E> {
        self.0.extend_from_slice(bytes);
        Ok(())
    }

    fn visit_seq<S: SeqAccess<'de>>(self, mut seq: S) -> Result<Self::Value, S::Error> {
        while let Some(byte) = seq.next_element()? {
            self.0.push(byte);
        }
        Ok(())
    }
}

impl ToBytes for () {
    #[inline]
    fn write_le<W: Write>(&self, _writer: W) -> IoResult<()> {
        Ok(())
    }
}

impl FromBytes for () {
    #[inline]
    fn read_le<R: Read>(_bytes: R) -> IoResult<Self> {
        Ok(())
    }
}

impl ToBytes for bool {
    #[inline]
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()> {
        u8::write_le(&(*self as u8), writer)
    }
}

impl FromBytes for bool {
    #[inline]
    fn read_le<R: Read>(reader: R) -> IoResult<Self> {
        match u8::read_le(reader) {
            Ok(0) => Ok(false),
            Ok(1) => Ok(true),
            Ok(_) => Err(error("FromBytes::read failed")),
            Err(err) => Err(err),
        }
    }
}

macro_rules! impl_bytes_for_integer {
    ($int:ty) => {
        impl ToBytes for $int {
            #[inline]
            fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
                writer.write_all(&self.to_le_bytes())
            }
        }

        impl FromBytes for $int {
            #[inline]
            fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
                let mut bytes = [0u8; core::mem::size_of::<$int>()];
                reader.read_exact(&mut bytes)?;
                Ok(<$int>::from_le_bytes(bytes))
            }
        }
    };
}

impl_bytes_for_integer!(u8);
impl_bytes_for_integer!(u16);
impl_bytes_for_integer!(u32);
impl_bytes_for_integer!(u64);
impl_bytes_for_integer!(u128);

impl_bytes_for_integer!(i8);
impl_bytes_for_integer!(i16);
impl_bytes_for_integer!(i32);
impl_bytes_for_integer!(i64);
impl_bytes_for_integer!(i128);

impl<const N: usize> ToBytes for [u8; N] {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        writer.write_all(self)
    }
}

impl<const N: usize> FromBytes for [u8; N] {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let mut arr = [0u8; N];
        reader.read_exact(&mut arr)?;
        Ok(arr)
    }
}

macro_rules! impl_bytes_for_integer_array {
    ($int:ty) => {
        impl<const N: usize> ToBytes for [$int; N] {
            #[inline]
            fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
                for num in self {
                    writer.write_all(&num.to_le_bytes())?;
                }
                Ok(())
            }
        }

        impl<const N: usize> FromBytes for [$int; N] {
            #[inline]
            fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
                let mut res: [$int; N] = [0; N];
                for num in res.iter_mut() {
                    let mut bytes = [0u8; core::mem::size_of::<$int>()];
                    reader.read_exact(&mut bytes)?;
                    *num = <$int>::from_le_bytes(bytes);
                }
                Ok(res)
            }
        }
    };
}

// u8 has a dedicated, faster implementation above
impl_bytes_for_integer_array!(u16);
impl_bytes_for_integer_array!(u32);
impl_bytes_for_integer_array!(u64);

impl<L: ToBytes, R: ToBytes> ToBytes for (L, R) {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)?;
        self.1.write_le(&mut writer)?;
        Ok(())
    }
}

impl<L: FromBytes, R: FromBytes> FromBytes for (L, R) {
    #[inline]
    fn read_le<Reader: Read>(mut reader: Reader) -> IoResult<Self> {
        let left: L = FromBytes::read_le(&mut reader)?;
        let right: R = FromBytes::read_le(&mut reader)?;
        Ok((left, right))
    }
}

impl<T: ToBytes> ToBytes for Vec<T> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        for item in self {
            item.write_le(&mut writer)?;
        }
        Ok(())
    }
}

impl<'a, T: 'a + ToBytes> ToBytes for &'a [T] {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        for item in *self {
            item.write_le(&mut writer)?;
        }
        Ok(())
    }
}

impl<'a, T: 'a + ToBytes> ToBytes for &'a T {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (*self).write_le(&mut writer)
    }
}

#[cfg(test)]
mod test {
    use super::ToBytes;
    use crate::Vec;

    #[test]
    fn test_macro_empty() {
        let array: Vec<u8> = vec![];
        let bytes_a: Vec<u8> = to_bytes_le![array].unwrap();
        assert_eq!(&array, &bytes_a);
        assert_eq!(0, bytes_a.len());

        let bytes_b: Vec<u8> = array.to_bytes_le().unwrap();
        assert_eq!(&array, &bytes_b);
        assert_eq!(0, bytes_b.len());
    }

    #[test]
    fn test_macro() {
        let array1 = [1u8; 32];
        let array2 = [2u8; 16];
        let array3 = [3u8; 8];
        let bytes = to_bytes_le![array1, array2, array3].unwrap();
        assert_eq!(bytes.len(), 56);

        let mut actual_bytes = Vec::new();
        actual_bytes.extend_from_slice(&array1);
        actual_bytes.extend_from_slice(&array2);
        actual_bytes.extend_from_slice(&array3);
        assert_eq!(bytes, actual_bytes);
    }
}
