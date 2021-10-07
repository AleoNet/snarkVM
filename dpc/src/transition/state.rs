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

use crate::prelude::*;

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    Debug(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct State<N: Network> {
    pub(super) transition: Transition<N>,
    #[derivative(PartialEq = "ignore", Debug = "ignore")]
    pub(super) executable: Executable<N>,
    pub(super) input_records: Vec<Record<N>>,
    pub(super) output_records: Vec<Record<N>>,
    pub(crate) ciphertext_randomizers: Vec<CiphertextRandomizer<N>>,
    pub(super) noop_signatures: Vec<Option<N::AccountSignature>>,
    pub(super) memo: Memo<N>,
}

impl<N: Network> State<N> {
    /// Returns a new state transition with no operations performed.
    pub fn new_noop<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self> {
        Ok(Self::builder().build(rng)?)
    }

    /// Returns a new state transition that mints the given amount to the recipient.
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        Ok(Self::builder()
            .add_output(Output::new(recipient, amount, Payload::default(), None)?)
            .build(rng)?)
    }

    /// Returns a new state transition that transfers a given amount of Aleo credits from a sender to a recipient.
    pub fn new_transfer<R: Rng + CryptoRng>(
        sender: &PrivateKey<N>,
        records: &Vec<Record<N>>,
        recipient: Address<N>,
        amount: AleoAmount,
        fee: AleoAmount,
        rng: &mut R,
    ) -> Result<Self> {
        assert!(records.len() <= N::NUM_INPUT_RECORDS);

        // Calculate the available balance of the sender.
        let mut balance = AleoAmount::ZERO;
        let mut inputs = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for record in records {
            balance = balance.add(AleoAmount::from_bytes(record.value() as i64));
            inputs.push(Input::new(&sender.to_compute_key()?, record.clone())?);
        }

        // Ensure the sender has sufficient balance.
        let total_cost = amount.add(fee);
        if balance < total_cost {
            return Err(anyhow!("Sender(s) has insufficient balance"));
        }

        // Construct the sender output.
        let sender_output = Output::new(
            Address::from_private_key(sender)?,
            balance.sub(total_cost),
            Payload::default(),
            None,
        )?;

        // Construct the recipient output.
        let recipient_output = Output::new(recipient, amount, Payload::default(), None)?;

        Ok(Self::builder()
            .add_inputs(inputs)
            .add_output(sender_output)
            .add_output(recipient_output)
            .build(rng)?)
    }

    /// Returns a new instance of `StateBuilder`.
    pub fn builder() -> TransitionBuilder<N> {
        TransitionBuilder::new()
    }

    /// Returns a reference to the transition.
    pub fn transition(&self) -> &Transition<N> {
        &self.transition
    }

    /// Returns a reference to the executable.
    pub fn executable(&self) -> &Executable<N> {
        &self.executable
    }

    /// Returns a reference to the input records.
    pub fn input_records(&self) -> &Vec<Record<N>> {
        &self.input_records
    }

    /// Returns a reference to the output records.
    pub fn output_records(&self) -> &Vec<Record<N>> {
        &self.output_records
    }

    /// Returns a reference to the noop signatures.
    pub fn noop_signatures(&self) -> &Vec<Option<N::AccountSignature>> {
        &self.noop_signatures
    }

    /// Returns a reference to the memo.
    pub fn memo(&self) -> &Memo<N> {
        &self.memo
    }
}

// TODO (howardwu): TEMPORARY - Add an is_valid method, call it in InnerPrivateVariables.
// assert!(kernel.is_valid());
// assert_eq!(N::NUM_INPUT_RECORDS, input_records.len());
// assert_eq!(N::NUM_INPUT_RECORDS, signatures.len());
// assert_eq!(N::NUM_OUTPUT_RECORDS, output_records.len());
// assert_eq!(N::NUM_OUTPUT_RECORDS, encrypted_record_randomizers.len());
