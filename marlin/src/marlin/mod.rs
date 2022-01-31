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

/// The Marlin circuit proving key.
mod circuit_proving_key;
pub use circuit_proving_key::*;

/// The Marlin circuit verifying key.
mod circuit_verifying_key;
pub use circuit_verifying_key::*;

/// Errors.
mod errors;
pub use errors::*;

/// A generic implementation of the Marlin proof system.
mod marlin;
pub use marlin::*;

/// Specifies the Marlin mode.
mod mode;
pub use mode::*;

/// The Marlin prepared circuit verifying key.
mod prepared_circuit_verifying_key;
pub use prepared_circuit_verifying_key::*;

/// The Marlin zkSNARK proof.
mod proof;
pub use proof::*;

/// Implementation of the `SNARK` trait for [`MarlinSNARK`].
mod snark;
pub use snark::*;

#[cfg(test)]
pub mod tests;

/// The Marlin universal SRS.
mod universal_srs;
pub use universal_srs::*;
