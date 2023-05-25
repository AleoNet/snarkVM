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
