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
    io::{Read, Result as IoResult, Write},
    Vec,
};

#[inline]
pub fn from_bytes_le_to_bits_le(bytes: &[u8]) -> impl Iterator<Item = bool> + '_ {
    bytes
        .iter()
        .map(|byte| (0..8).map(move |i| (*byte >> i) & 1 == 1))
        .flatten()
}

#[inline]
pub fn from_bits_le_to_bytes_le(bits: &[bool]) -> Vec<u8> {
    // Pad the bits if it not a correct size
    let mut bits = std::borrow::Cow::from(bits);
    if bits.len() % 8 != 0 {
        let current_length = bits.len();
        bits.to_mut().resize(current_length + 8 - (current_length % 8), false);
    }

    let mut bytes = Vec::with_capacity(bits.len() / 8);
    for bits in bits.chunks(8) {
        let mut result = 0u8;
        for (i, bit) in bits.iter().enumerate() {
            let bit_value = *bit as u8;
            result += bit_value << i as u8;
        }
        bytes.push(result);
    }
    bytes
}

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

pub trait ToBytes: Sized {
    /// Writes `self` into `writer` as little-endian bytes.
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()>;

    /// Returns `self` as a byte array in little-endian order.
    fn to_bytes_le(&self) -> anyhow::Result<Vec<u8>> {
        Ok(to_bytes_le![self]?)
    }
}

pub trait FromBytes: Sized {
    /// Reads `Self` from `reader` as little-endian bytes.
    fn read_le<R: Read>(reader: R) -> IoResult<Self>;

    /// Returns `Self` from a byte array in little-endian order.
    fn from_bytes_le(bytes: &[u8]) -> anyhow::Result<Self> {
        Ok(Self::read_le(bytes)?)
    }
}

macro_rules! to_bytes_for_int_array {
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

// u8 has a dedicated, faster implementation
to_bytes_for_int_array!(u16);
to_bytes_for_int_array!(u32);
to_bytes_for_int_array!(u64);

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

impl<L: ToBytes, R: ToBytes> ToBytes for (L, R) {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.0.write_le(&mut writer)?;
        self.1.write_le(&mut writer)?;
        Ok(())
    }
}

macro_rules! to_bytes_for_integer {
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

to_bytes_for_integer!(u8);
to_bytes_for_integer!(u16);
to_bytes_for_integer!(u32);
to_bytes_for_integer!(u64);
to_bytes_for_integer!(u128);

to_bytes_for_integer!(i64);

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
    use super::{from_bits_le_to_bytes_le, from_bytes_le_to_bits_le, ToBytes};
    use crate::Vec;

    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;

    const ITERATIONS: usize = 1000;

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

    #[test]
    fn test_from_bytes_le_to_bits_le() {
        assert_eq!(from_bytes_le_to_bits_le(&[204, 76]).collect::<Vec<bool>>(), [
            false, false, true, true, false, false, true, true, // 204
            false, false, true, true, false, false, true, false, // 76
        ]);
    }

    #[test]
    fn test_from_bits_le_to_bytes_le() {
        let bits = [
            false, false, true, true, false, false, true, true, // 204
            false, false, true, true, false, false, true, false, // 76
        ];
        assert_eq!(from_bits_le_to_bytes_le(&bits), [204, 76]);
    }

    #[test]
    fn test_from_bits_le_to_bytes_le_roundtrip() {
        let mut rng = XorShiftRng::seed_from_u64(1231275789u64);

        for _ in 0..ITERATIONS {
            let given_bytes: [u8; 32] = rng.gen();

            let bits = from_bytes_le_to_bits_le(&given_bytes).collect::<Vec<_>>();
            let recovered_bytes = from_bits_le_to_bytes_le(&bits);

            assert_eq!(given_bytes.to_vec(), recovered_bytes);
        }
    }
}
