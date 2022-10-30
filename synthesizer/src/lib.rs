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

#![forbid(unsafe_code)]
#![allow(clippy::module_inception)]
#![allow(clippy::single_element_loop)]
// TODO (howardwu): Remove me after tracing.
#![allow(clippy::print_in_format_impl)]
#![cfg_attr(test, allow(clippy::assertions_on_result_states))]

#[macro_use]
extern crate tracing;

pub mod block;
pub use block::*;

pub mod coinbase_puzzle;
pub use coinbase_puzzle::*;

pub mod process;
pub use process::*;

pub mod program;
pub use program::*;

pub mod snark;
pub use snark::*;

pub mod store;
pub use store::*;

pub mod vm;
pub use vm::*;

/// The circuit for state path verification.
pub fn inject_and_verify_state_path<N: console::network::Network, A: circuit::Aleo<Network = N>>(
    state_path: console::program::StatePath<N>,
    commitment: console::types::Field<N>,
) {
    use circuit::Inject;

    // Allocate the state path circuit.
    let state_path_circuit = circuit::StatePath::<A>::new(circuit::Mode::Private, state_path);
    // Allocate the commitment circuit.
    let commitment_circuit = circuit::Field::<A>::new(circuit::Mode::Private, commitment);

    A::assert_eq(state_path_circuit.transition_leaf().id(), commitment_circuit);

    A::assert(state_path_circuit.verify())
}
