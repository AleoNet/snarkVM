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

use crate::Record;
use snarkvm_console_account::PrivateKey;
use snarkvm_console_network::Network;

use anyhow::Result;

pub struct Execution;

pub struct Function<N: Network> {
    /// The execution proof.
    execution: Execution,
    /// The process root.
    root: N::Field,
}

pub struct Inputs<N: Network> {
    /// The serial numbers of the inputs.
    serial_numbers: Vec<N::Field>,
}

pub struct Outputs<N: Network> {
    /// The commitments from the outputs.
    commitments: Vec<N::Field>,
    /// The records from the outputs.
    records: Vec<Record<N>>,
    // /// The record data from the outputs.
    // data: Vec<Data<N>>,
}

pub struct Transition<N: Network> {
    /// The program that was referenced.
    program: N::Field,
    /// The process that was instantiated.
    process: N::Field,
    /// The function that was executed.
    function: Function<N>,
    /// The inputs of the function.
    inputs: Inputs<N>,
    /// The outputs of the function.
    outputs: Outputs<N>,
    /// The net difference between the input and output balances.
    fee: u64,
}

// impl<N: Network> Transition<N> {
//     pub fn new(
//         private_key: PrivateKey<N>,
//         root: N::Field,
//         inputs: &[Record<N>],
//         outputs: &[Record<N>],
//     ) -> Result<Self> {
//     }
// }
