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

/// The Marlin certificate.
pub(super) mod certificate;
pub use certificate::*;

/// The Marlin circuit proving key.
pub(super) mod circuit_proving_key;
pub use circuit_proving_key::*;

/// The Marlin circuit verifying key.
pub(super) mod circuit_verifying_key;
pub use circuit_verifying_key::*;

/// The Marlin prepared circuit verifying key.
pub(super) mod prepared_circuit_verifying_key;
pub use prepared_circuit_verifying_key::*;

/// The Marlin zkSNARK proof.
pub(super) mod proof;
pub use proof::*;

/// A test circuit.
pub(super) mod test_circuit;
pub use test_circuit::*;

/// The Marlin universal SRS.
pub(super) mod universal_srs;
pub use universal_srs::*;
