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

/// Gadget for an optionally hiding Marlin-KZG10 commitment.
pub mod commitment;

// mod labeled_commitment;
// pub use labeled_commitment::*;
//
// mod prepared_commitment;
// pub use prepared_commitment::*;
//
// mod prepared_labeled_commitment;
// pub use prepared_labeled_commitment::*;

/// Prepared verifier key gadget for the Marlin-KZG10 polynomial commitment scheme.
pub mod prepared_verifier_key;

/// Verifier key gadge for the Marlin-KZG10 polynomial commitment scheme.
mod verifier_key;
pub(crate) use verifier_key::*;
