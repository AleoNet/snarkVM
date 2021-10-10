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

pub mod amount;
pub use amount::*;

pub mod event;
pub use event::*;

pub mod function_inputs;
pub use function_inputs::*;

pub mod function_type;
pub use function_type::*;

pub(crate) mod local_commitments;
pub(crate) use local_commitments::*;

pub mod local_proof;
pub use local_proof::*;

pub mod noop;
pub use noop::*;

pub mod operation;
pub use operation::*;

pub mod program;
pub use program::*;

pub mod program_public_variables;
pub use program_public_variables::*;

pub mod request;
pub use request::*;

pub mod response;
pub use response::*;

pub mod virtual_machine;
pub use virtual_machine::*;

use crate::Network;
use snarkvm_algorithms::{merkle_tree::MerklePath, prelude::*};

/// Program ID, program path, verifying key, and proof.
#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct Execution<N: Network> {
    pub program_id: N::ProgramID,
    pub program_path: MerklePath<N::ProgramFunctionsTreeParameters>,
    pub verifying_key: N::ProgramVerifyingKey,
    pub proof: <N::ProgramSNARK as SNARK>::Proof,
}
