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

use crate::Parameters;
use snarkvm_algorithms::{merkle_tree::MerklePath, SNARK};

/// Program index, path, verifying key, and proof.
#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct Execution<C: Parameters> {
    pub program_path: MerklePath<C::ProgramCircuitTreeParameters>,
    pub verifying_key: <C::ProgramSNARK as SNARK>::VerifyingKey,
    pub proof: <C::ProgramSNARK as SNARK>::Proof,
}
