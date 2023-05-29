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
