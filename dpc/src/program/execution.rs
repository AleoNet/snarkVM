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

use crate::Network;
use snarkvm_algorithms::{merkle_tree::MerklePath, SNARK};

/// Program index, path, verifying key, and proof.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct Execution<N: Network> {
    pub program_path: MerklePath<N::ProgramCircuitTreeParameters>,
    pub verifying_key: <N::ProgramSNARK as SNARK>::VerifyingKey,
    pub proof: <N::ProgramSNARK as SNARK>::Proof,
}

#[derive(Clone)]
pub enum ExecutionType {
    Noop,
    Add,
    Update,
    Remove,
    Join,
    Split,
    JoinSplit,
}

impl ExecutionType {
    pub fn input_count(&self) -> u8 {
        match self {
            Self::Noop => 0,
            Self::Add => 0,
            Self::Update => 1,
            Self::Remove => 1,
            Self::Join => 2,
            Self::Split => 1,
            Self::JoinSplit => 2,
        }
    }

    pub fn output_count(&self) -> u8 {
        match self {
            Self::Noop => 0,
            Self::Add => 1,
            Self::Update => 1,
            Self::Remove => 0,
            Self::Join => 1,
            Self::Split => 2,
            Self::JoinSplit => 2,
        }
    }
}
