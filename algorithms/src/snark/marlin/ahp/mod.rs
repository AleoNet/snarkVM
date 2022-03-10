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

/// Algebraic holographic proofs.
pub mod ahp;
pub use ahp::*;

/// Errors.
pub mod errors;
pub use errors::*;

/// Describes data structures and the algorithms used by the AHP indexer.
pub mod indexer;
pub(crate) use indexer::*;

pub(crate) mod matrices;

/// Describes data structures and the algorithms used by the AHP prover.
pub mod prover;

/// Describes data structures and the algorithms used by the AHP verifier.
pub mod verifier;
