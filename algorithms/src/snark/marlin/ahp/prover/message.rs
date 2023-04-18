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

use snarkvm_fields::PrimeField;
use snarkvm_utilities::{error, serialize::*, ToBytes, Write};

#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct MatrixSums<F: PrimeField> {
    pub sum_a: F,
    pub sum_b: F,
    pub sum_c: F,
}

/// The prover message in the third round.
#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ThirdMessage<F: PrimeField> {
    pub sums: Vec<MatrixSums<F>>,
}

impl<F: PrimeField> ToBytes for ThirdMessage<F> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize_compressed(self, &mut w).map_err(|_| error("Could not serialize ProverMsg"))
    }
}
