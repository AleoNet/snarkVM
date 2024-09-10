// Copyright 2024 Aleo Network Foundation
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

/// The Varuna certificate.
pub(super) mod certificate;
pub use certificate::*;

/// The Varuna circuit proving key.
pub(super) mod circuit_proving_key;
pub use circuit_proving_key::*;

/// The Varuna circuit verifying key.
pub(super) mod circuit_verifying_key;
pub use circuit_verifying_key::*;

/// The Varuna zkSNARK proof.
pub(super) mod proof;
pub use proof::*;

/// A test circuit.
#[cfg(any(test, feature = "test"))]
pub(super) mod test_circuit;
#[cfg(any(test, feature = "test"))]
pub use test_circuit::*;

/// The Varuna universal SRS.
pub type UniversalSRS<E> = crate::polycommit::sonic_pc::UniversalParams<E>;
