// Copyright (C) 2019-2023 Aleo Systems Inc.
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

#[derive(Error, Debug)]
pub enum SerializationError {
    #[error("{}", _0)]
    AnyhowError(#[from] anyhow::Error),
    /// During serialization with bincode, we encountered a serialization issue
    #[error(transparent)]
    BincodeError(#[from] bincode::Error),
    /// During serialization we could not serialize to the right sized int
    #[error(transparent)]
    IntError(#[from] std::num::TryFromIntError),
    /// During serialization, the data was invalid.
    #[error("the input buffer contained invalid data")]
    InvalidData,
    /// During serialization, we countered an I/O error.
    #[error("IoError: {0}")]
    IoError(#[from] crate::io::Error),
    /// During serialization, we didn't have enough space to write extra info.
    #[error("the last byte does not have enough space to encode the extra info bits")]
    NotEnoughSpace,
    /// During serialization, non-empty flags were given where none were
    /// expected.
    #[error("the call expects empty flags")]
    UnexpectedFlags,
    /// During serialization, the target was found to be incompatible
    #[error("the value was serialized on a target that is incompatible with the current target")]
    IncompatibleTarget,
}

impl From<SerializationError> for crate::io::Error {
    fn from(error: SerializationError) -> Self {
        crate::io::Error::new(crate::io::ErrorKind::Other, format!("{error}"))
    }
}
