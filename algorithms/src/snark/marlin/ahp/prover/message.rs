// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use crate::snark::marlin::{ahp::indexer::Circuit, MarlinMode};

use snarkvm_fields::PrimeField;
use snarkvm_utilities::{error, serialize::*, ToBytes, Write};

use std::collections::BTreeMap;

#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct MatrixSums<F: std::marker::Sync> {
    pub sum_a: F,
    pub sum_b: F,
    pub sum_c: F,
}

/// The prover message in the third round.
#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ThirdMessage<'b, F: PrimeField, MM: std::marker::Sync + MarlinMode> {
    pub sums: BTreeMap<&'b Circuit<F, MM>, MatrixSums<F>>,
}

impl<'b, F: PrimeField, MM: MarlinMode> ToBytes for ThirdMessage<'b, F, MM> {
    fn write_le<W: Write>(&self, mut w: W) -> io::Result<()> {
        CanonicalSerialize::serialize_compressed(self, &mut w).map_err(|_| error("Could not serialize ProverMsg"))
    }
}
