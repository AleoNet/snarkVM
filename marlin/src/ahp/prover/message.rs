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

use crate::Vec;
use snarkvm_fields::Field;
use snarkvm_utilities::{bytes::ToBytes, errors::SerializationError, serialize::*, Write};

/// Each prover message that is not a list of oracles is a list of field elements.
#[derive(Clone, Debug)]
pub enum ProverMessage<F: Field> {
    /// Some rounds, the prover sends only oracles. (This is actually the case for all
    /// rounds in Marlin.)
    EmptyMessage,
    /// Otherwise, it's one or more field elements.
    FieldElements(Vec<F>),
}

impl<F: Field> ToBytes for ProverMessage<F> {
    fn write<W: Write>(&self, w: W) -> io::Result<()> {
        match self {
            ProverMessage::EmptyMessage => Ok(()),
            ProverMessage::FieldElements(field_elems) => field_elems.write(w),
        }
    }
}

impl<F: Field> CanonicalSerialize for ProverMessage<F> {
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        let res: Option<Vec<F>> = match self {
            ProverMessage::EmptyMessage => None,
            ProverMessage::FieldElements(v) => Some(v.clone()),
        };
        res.serialize(writer)
    }

    fn serialized_size(&self) -> usize {
        let res: Option<Vec<F>> = match self {
            ProverMessage::EmptyMessage => None,
            ProverMessage::FieldElements(v) => Some(v.clone()),
        };
        res.serialized_size()
    }

    // fn serialize_unchecked<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
    //     let res: Option<Vec<F>> = match self {
    //         ProverMessage::EmptyMessage => None,
    //         ProverMessage::FieldElements(v) => Some(v.clone()),
    //     };
    //     res.serialize_unchecked(writer)
    // }

    fn serialize_uncompressed<W: Write>(&self, writer: &mut W) -> Result<(), SerializationError> {
        let res: Option<Vec<F>> = match self {
            ProverMessage::EmptyMessage => None,
            ProverMessage::FieldElements(v) => Some(v.clone()),
        };
        res.serialize_uncompressed(writer)
    }

    fn uncompressed_size(&self) -> usize {
        let res: Option<Vec<F>> = match self {
            ProverMessage::EmptyMessage => None,
            ProverMessage::FieldElements(v) => Some(v.clone()),
        };
        res.uncompressed_size()
    }
}

impl<F: Field> CanonicalDeserialize for ProverMessage<F> {
    fn deserialize<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let res = Option::<Vec<F>>::deserialize(reader)?;

        if let Some(res) = res {
            Ok(ProverMessage::FieldElements(res))
        } else {
            Ok(ProverMessage::EmptyMessage)
        }
    }

    // fn deserialize_unchecked<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
    //     let res = Option::<Vec<F>>::deserialize_unchecked(reader)?;
    //
    //     if let Some(res) = res {
    //         Ok(ProverMessage::FieldElements(res))
    //     } else {
    //         Ok(ProverMessage::EmptyMessage)
    //     }
    // }

    fn deserialize_uncompressed<R: Read>(reader: &mut R) -> Result<Self, SerializationError> {
        let res = Option::<Vec<F>>::deserialize_uncompressed(reader)?;

        if let Some(res) = res {
            Ok(ProverMessage::FieldElements(res))
        } else {
            Ok(ProverMessage::EmptyMessage)
        }
    }
}
