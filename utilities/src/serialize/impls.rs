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

pub use crate::{
    io::{
        Read,
        Write,
        {self},
    },
    ops::Range,
    FromBytes,
    ToBytes,
    Vec,
};
use crate::{serialize::traits::*, SerializationError};

use std::{borrow::Cow, collections::BTreeMap, rc::Rc, sync::Arc};

impl CanonicalSerialize for bool {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        Ok(self.write_le(writer)?)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        1
    }
}

impl CanonicalDeserialize for bool {
    #[inline]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(bool::read_le(reader)?)
    }
}

impl CanonicalSerialize for String {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        Ok(bincode::serialize_into(writer, self)?)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        self.len() + 8
    }
}

impl CanonicalDeserialize for String {
    #[inline]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(bincode::deserialize_from(reader)?)
    }
}

macro_rules! impl_canonical_serialization_uint {
    ($type:ty) => {
        impl CanonicalSerialize for $type {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
                Ok(writer.write_all(&self.to_le_bytes())?)
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                Self::SERIALIZED_SIZE
            }
        }

        impl ConstantSerializedSize for $type {
            const SERIALIZED_SIZE: usize = std::mem::size_of::<$type>();
            const UNCOMPRESSED_SIZE: usize = Self::SERIALIZED_SIZE;
        }

        impl CanonicalDeserialize for $type {
            #[inline]
            fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
                let mut bytes = [0u8; Self::SERIALIZED_SIZE];
                reader.read_exact(&mut bytes)?;
                Ok(<$type>::from_le_bytes(bytes))
            }
        }
    };
}

impl_canonical_serialization_uint!(u8);
impl_canonical_serialization_uint!(u16);
impl_canonical_serialization_uint!(u32);
impl_canonical_serialization_uint!(u64);
impl_canonical_serialization_uint!(usize);

impl<T: CanonicalSerialize> CanonicalSerialize for Option<T> {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.is_some().serialize(writer)?;
        if let Some(item) = self {
            item.serialize(writer)?;
        }

        Ok(())
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        8 + if let Some(item) = self {
            item.serialized_size()
        } else {
            0
        }
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.is_some().serialize_uncompressed(writer)?;
        if let Some(item) = self {
            item.serialize_uncompressed(writer)?;
        }

        Ok(())
    }
}

impl<T: CanonicalDeserialize> CanonicalDeserialize for Option<T> {
    #[inline]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let is_some = bool::deserialize(reader)?;
        let data = if is_some { Some(T::deserialize(reader)?) } else { None };

        Ok(data)
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let is_some = bool::deserialize(reader)?;
        let data = if is_some {
            Some(T::deserialize_uncompressed(reader)?)
        } else {
            None
        };

        Ok(data)
    }
}

// No-op
impl<T> CanonicalSerialize for std::marker::PhantomData<T> {
    #[inline]
    fn serialize<W: Write>(&self, _writer: &mut W) -> Result<(), SerializationError> {
        Ok(())
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        0
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, _writer: &mut W) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl<T> CanonicalDeserialize for std::marker::PhantomData<T> {
    #[inline]
    fn deserialize<R: Read>(_reader: &mut R) -> Result<Self, SerializationError> {
        Ok(std::marker::PhantomData)
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(_reader: &mut R) -> Result<Self, SerializationError> {
        Ok(std::marker::PhantomData)
    }
}

impl<T: CanonicalSerialize + ToOwned> CanonicalSerialize for Rc<T> {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_ref().serialize(writer)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        self.as_ref().serialized_size()
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_ref().serialize_uncompressed(writer)
    }
}

impl<T: CanonicalDeserialize + ToOwned> CanonicalDeserialize for Rc<T> {
    #[inline]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(Rc::new(T::deserialize(reader)?))
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(Rc::new(T::deserialize_uncompressed(reader)?))
    }
}

impl<T: CanonicalSerialize + ToOwned> CanonicalSerialize for Arc<T> {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_ref().serialize(writer)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        self.as_ref().serialized_size()
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_ref().serialize_uncompressed(writer)
    }
}

impl<T: CanonicalDeserialize + ToOwned> CanonicalDeserialize for Arc<T> {
    #[inline]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(Arc::new(T::deserialize(reader)?))
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(Arc::new(T::deserialize_uncompressed(reader)?))
    }
}

impl<'a, T: CanonicalSerialize + ToOwned> CanonicalSerialize for Cow<'a, T> {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_ref().serialize(writer)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        self.as_ref().serialized_size()
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_ref().serialize_uncompressed(writer)
    }
}

impl<'a, T> CanonicalDeserialize for Cow<'a, T>
where
    T: ToOwned,
    <T as ToOwned>::Owned: CanonicalDeserialize,
{
    #[inline]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(Cow::Owned(<T as ToOwned>::Owned::deserialize(reader)?))
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        Ok(Cow::Owned(<T as ToOwned>::Owned::deserialize_uncompressed(reader)?))
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for Vec<T> {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_slice().serialize(writer)
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        self.as_slice().serialized_size()
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.as_slice().serialize_uncompressed(writer)
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        self.as_slice().uncompressed_size()
    }
}

impl<T: CanonicalDeserialize> CanonicalDeserialize for Vec<T> {
    #[inline]
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let len = u64::deserialize(reader)?;
        let mut values = Vec::with_capacity(len as usize);
        for _ in 0..len {
            values.push(T::deserialize(reader)?);
        }
        Ok(values)
    }

    #[inline]
    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let len = u64::deserialize(reader)?;
        let mut values = Vec::with_capacity(len as usize);
        for _ in 0..len {
            values.push(T::deserialize_uncompressed(reader)?);
        }
        Ok(values)
    }
}

impl<T: CanonicalSerialize> CanonicalSerialize for [T] {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        let len = self.len() as u64;
        len.serialize(writer)?;
        for item in self.iter() {
            item.serialize(writer)?;
        }
        Ok(())
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        8 + self.iter().map(|item| item.serialized_size()).sum::<usize>()
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        let len = self.len() as u64;
        len.serialize(writer)?;
        for item in self.iter() {
            item.serialize_uncompressed(writer)?;
        }
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        8 + self.iter().map(|item| item.uncompressed_size()).sum::<usize>()
    }
}

impl<'a, T: CanonicalSerialize> CanonicalSerialize for &'a [T] {
    #[inline]
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        let len = self.len() as u64;
        len.serialize(writer)?;
        for item in self.iter() {
            item.serialize(writer)?;
        }
        Ok(())
    }

    #[inline]
    fn serialized_size(&self) -> usize {
        8 + self.iter().map(|item| item.serialized_size()).sum::<usize>()
    }

    #[inline]
    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        let len = self.len() as u64;
        len.serialize(writer)?;
        for item in self.iter() {
            item.serialize_uncompressed(writer)?;
        }
        Ok(())
    }

    #[inline]
    fn uncompressed_size(&self) -> usize {
        8 + self.iter().map(|item| item.uncompressed_size()).sum::<usize>()
    }
}

// Implement Serialization for tuples
macro_rules! impl_tuple {
    ($( $ty: ident : $no: tt, )+) => {
        impl<$($ty, )+> CanonicalSerialize for ($($ty,)+) where
            $($ty: CanonicalSerialize,)+
        {
            #[inline]
            fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
                $(self.$no.serialize(writer)?;)*
                Ok(())
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                [$(
                    self.$no.serialized_size(),
                )*].iter().sum()
            }

            #[inline]
            fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
                $(self.$no.serialize_uncompressed(writer)?;)*
                Ok(())
            }

            #[inline]
            fn uncompressed_size(&self) -> usize {
                [$(
                    self.$no.uncompressed_size(),
                )*].iter().sum()
            }
        }

        impl<$($ty, )+> CanonicalDeserialize for ($($ty,)+) where
            $($ty: CanonicalDeserialize,)+
        {
            #[inline]
            fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
                Ok(($(
                    $ty::deserialize(reader)?,
                )+))
            }

            #[inline]
            fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
                Ok(($(
                    $ty::deserialize_uncompressed(reader)?,
                )+))
            }
        }
    }
}

impl_tuple!(A:0, B:1,);
impl_tuple!(A:0, B:1, C:2,);
impl_tuple!(A:0, B:1, C:2, D:3,);

impl<K, V> CanonicalSerialize for BTreeMap<K, V>
where
    K: CanonicalSerialize,
    V: CanonicalSerialize,
{
    /// Serializes a `BTreeMap` as `len(map) || key 1 || value 1 || ... || key n || value n`.
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        let len = self.len() as u64;
        len.serialize(writer)?;
        for (k, v) in self.iter() {
            k.serialize(writer)?;
            v.serialize(writer)?;
        }
        Ok(())
    }

    fn serialized_size(&self) -> usize {
        8 + self
            .iter()
            .map(|(k, v)| k.serialized_size() + v.serialized_size())
            .sum::<usize>()
    }
}

impl<K, V> CanonicalDeserialize for BTreeMap<K, V>
where
    K: Ord + CanonicalDeserialize,
    V: CanonicalDeserialize,
{
    /// Deserializes a `BTreeMap` from `len(map) || key 1 || value 1 || ... || key n || value n`.
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let len = u64::deserialize(reader)?;
        let mut map = BTreeMap::new();
        for _ in 0..len {
            map.insert(K::deserialize(reader)?, V::deserialize(reader)?);
        }
        Ok(map)
    }
}

impl<T> CanonicalSerialize for Range<T>
where
    T: CanonicalSerialize,
{
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        self.start.serialize(writer)?;
        self.end.serialize(writer)
    }

    fn serialized_size(&self) -> usize {
        self.start.serialized_size() + self.end.serialized_size()
    }
}

impl<T> CanonicalDeserialize for Range<T>
where
    T: CanonicalDeserialize,
{
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let start = T::deserialize(reader)?;
        let end = T::deserialize(reader)?;

        Ok(Self {
            start,
            end
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn test_serialize<T: PartialEq + std::fmt::Debug + CanonicalSerialize + CanonicalDeserialize>(data: T) {
        let mut serialized = vec![0; data.serialized_size()];
        data.serialize(&mut &mut serialized[..]).unwrap();
        let de = T::deserialize(&mut &serialized[..]).unwrap();
        assert_eq!(data, de);
    }

    #[test]
    fn test_bool() {
        test_serialize(true);
        test_serialize(false);
    }

    #[test]
    fn test_uint() {
        test_serialize(192830918usize);
        test_serialize(192830918u64);
        test_serialize(192830918u32);
        test_serialize(22313u16);
        test_serialize(123u8);
    }

    #[test]
    fn test_string() {
        test_serialize("asdf".to_owned());
    }

    #[test]
    fn test_vec() {
        test_serialize(vec![1u64, 2, 3, 4, 5]);
        test_serialize(Vec::<u64>::new());
    }

    #[test]
    fn test_tuple() {
        test_serialize((123u64, 234u32, 999u16));
    }

    #[test]
    fn test_tuple_vec() {
        test_serialize(vec![
            (123u64, 234u32, 999u16),
            (123u64, 234u32, 999u16),
            (123u64, 234u32, 999u16),
        ]);
    }

    #[test]
    fn test_option() {
        test_serialize(Some(3u32));
        test_serialize(None::<u32>);
    }

    #[test]
    fn test_phantomdata() {
        test_serialize(std::marker::PhantomData::<u64>);
    }
}
