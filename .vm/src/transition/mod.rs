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

pub mod input;
use input::*;

pub mod output;
use output::*;

pub mod proof;
use proof::*;

use console::{
    account::{Address, ComputeKey, PrivateKey, ViewKey},
    network::{prelude::*, Network},
    transition::{Record, State},
    types::{Field, Group, Scalar, U64},
};
use snarkvm_algorithms::snark::marlin::Proof;

// pub struct Execution;
//
// pub struct Function<N: Network> {
//     /// The execution proof.
//     execution: Execution,
// }

pub struct Transition<N: Network> {
    /// The program ID of the transition.
    pub program: Field<N>,
    /// The process ID of the transition.
    pub process: Field<N>,
    // /// The function that was executed.
    // function: Function<N>,
    /// The transition inputs.
    pub inputs: Vec<Input<N>>,
    /// The transition outputs.
    pub outputs: Vec<Output<N>>,
    /// The transition input proofs.
    pub input_proofs: Vec<Proof<snarkvm_curves::bls12_377::Bls12_377>>,
    /// The transition output proofs.
    pub output_proofs: Vec<Proof<snarkvm_curves::bls12_377::Bls12_377>>,
    /// The transition view key commitment (i.e. `tcm := Hash(caller, tpk, tvk)`).
    pub tcm: Field<N>,
    /// The transition public key (i.e. `tpk := Hash(r_tcm) * G`).
    pub tpk: Group<N>,
    /// The fee (i.e. `fee := Σ balance_in - Σ balance_out`).
    pub fee: i64,
}

impl<N: Network> Transition<N> {
    /// Returns `true` if the transition is valid.
    pub fn verify(&self) -> bool {
        // // Ensure the program and process ID matches for all outputs.
        // self.outputs.iter().all(|output| {})

        // self.
        true
    }

    /// Returns the serial numbers in the transition.
    pub fn serial_numbers(&self) -> Vec<Field<N>> {
        self.inputs.iter().map(Input::serial_number).collect::<Vec<_>>()
    }

    /// Returns the commitments in the transition.
    pub fn to_commitments(&self) -> Result<Vec<Field<N>>> {
        self.outputs.iter().map(Output::to_commitment).collect::<Result<Vec<_>>>()
    }

    /// Returns the fee commitment of this transition, where:
    ///   - `fcm := Σ bcm_in - Σ bcm_out - Commit(fee, 0) = Commit(0, r_fcm)`
    pub fn fcm(&self) -> Result<Group<N>> {
        let mut fcm = Group::<N>::zero();
        // Add the input balance commitments.
        self.inputs.iter().for_each(|input| fcm += input.bcm());
        // Subtract the output balance commitments.
        self.outputs.iter().for_each(|output| fcm -= output.bcm());
        // Subtract the fee to get the fee commitment.
        let fcm = match self.fee.is_positive() {
            true => fcm - N::commit_ped64(&self.fee.abs().to_bits_le(), &Scalar::zero())?,
            false => fcm + N::commit_ped64(&self.fee.abs().to_bits_le(), &Scalar::zero())?,
        };
        // Return the fee commitment.
        Ok(fcm)
    }
}
