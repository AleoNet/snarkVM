// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

/// An argument passed into a future.
#[derive(Clone)]
pub enum Argument<N: Network> {
    /// A plaintext value.
    Plaintext(Plaintext<N>),
    /// A future.
    Future(Future<N>),
}

impl<N: Network> FromBytes for Argument<N> {
    fn read_le<R: Read>(reader: R) -> IoResult<Self>
    where
        Self: Sized,
    {
        todo!()
    }
}

impl<N: Network> ToBytes for Argument<N> {
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()> {
        todo!()
    }
}

impl<N: Network> ToBits for Argument<N> {
    /// Returns the argument as a list of **little-endian** bits.
    #[inline]
    fn write_bits_le(&self, vec: &mut Vec<bool>) {
        todo!()
    }

    /// Returns the argument as a list of **big-endian** bits.
    #[inline]
    fn write_bits_be(&self, vec: &mut Vec<bool>) {
        todo!()
    }
}
