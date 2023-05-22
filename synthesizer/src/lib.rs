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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]
// #![warn(clippy::cast_possible_truncation)]
#![allow(clippy::single_element_loop)]
// TODO (howardwu): Remove me after tracing.
#![allow(clippy::print_in_format_impl)]
// TODO (howardwu): Update the return type on `execute` after stabilizing the interface.
#![allow(clippy::type_complexity)]

#[macro_use]
extern crate tracing;

#[cfg(feature = "coinbase")]
pub use snarkvm_synthesizer_coinbase as coinbase;

#[cfg(feature = "snark")]
pub use snarkvm_synthesizer_snark as snark;

pub mod block;
pub use block::*;

pub mod process;
pub use process::*;

pub mod program;
pub use program::*;

pub mod store;
pub use store::*;

pub mod vm;
pub use vm::*;

// /// Initializes a new **testing-only** instance of the ledger.
// pub fn new(rng: &mut TestRng) -> Result<Self> {
//     // Initialize the genesis block.
//     let genesis = synthesizer::vm::test_helpers::sample_genesis_block(rng);
//     // Initialize the ledger.
//     snarkvm_ledger::Ledger::load_unchecked(genesis, None)
// }

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::Circuit;
//     use snarkvm_utilities::rand::TestRng;
//
//     type CurrentAleo = Circuit;
//     type CurrentNetwork = <Circuit as Environment>::Network;
//
//     const ITERATIONS: usize = 100;
//
//     // use crate::snark::UniversalSRS;
//     fn check_batch_verify(mode: Mode, batch_size: usize) {
//         let rng = &mut TestRng::default();
//
//         // Initialize the ledger.
//         let ledger = crate::state_path::test_helpers::TestLedger::new(rng).unwrap();
//         // Retrieve the genesis block.
//         let genesis = ledger.get_block(0).unwrap();
//
//         // Construct the assignments.
//         let mut assignments = Vec::with_capacity(batch_size);
//
//         // Construct the verification inputs.
//         let mut inputs = vec![];
//
//         for _ in 0..batch_size {
//             let commitment = genesis.commitments().next().unwrap();
//             // Construct the console state path.
//             let console_state_path = ledger.get_state_path_for_commitment(commitment).unwrap();
//             // Construct the circuit state path.
//             let circuit_state_path = StatePath::<CurrentAleo>::new(mode, console_state_path.clone());
//
//             // Ensure the state path is valid.
//             let is_valid = circuit_state_path.verify();
//             assert!(is_valid.eject_value());
//             assert!(CurrentAleo::is_satisfied());
//
//             let assignment = CurrentAleo::eject_assignment_and_reset();
//             Circuit::reset();
//
//             inputs.push(vec![<Circuit as Environment>::BaseField::one(), **console_state_path.state_root]);
//
//             assignments.push(assignment);
//         }
//
//         // Construct the proving and verifying keys.
//         let universal_srs = UniversalSRS::<CurrentNetwork>::load().unwrap();
//         let function_name = format!("state_paths_{batch_size}");
//         let (proving_key, verifying_key) = universal_srs.to_circuit_key(function_name, &assignments[0]).unwrap();
//
//         // Generate the batch proof.
//         let batch_proof = proving_key.prove_batch(&function_name, &assignments, rng).unwrap();
//
//         // Verify the batch proof.
//         let batch_verify = verifying_key.verify_batch(&function_name, inputs.as_slice(), &batch_proof);
//         assert!(batch_verify);
//     }
//
//     #[test]
//     fn test_state_path_batch_1() {
//         check_batch_verify(Mode::Private, 1);
//     }
//
//     #[test]
//     fn test_state_path_batch_2() {
//         check_batch_verify(Mode::Private, 2);
//     }
//
//     #[test]
//     fn test_state_path_batch_4() {
//         check_batch_verify(Mode::Private, 4);
//     }
//
//     #[test]
//     fn test_state_path_batch_8() {
//         check_batch_verify(Mode::Private, 8);
//     }
// }
