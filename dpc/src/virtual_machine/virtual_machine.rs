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
// use snarkvm_algorithms::prelude::*;

use anyhow::Result;
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::collections::HashMap;

pub struct VirtualMachine<N: Network> {
    /// The request.
    request: Request<N>,
    /// The caller of the request.
    caller: Address<N>,
    /// The outputs balances.
    balances: HashMap<Address<N>, u64>,
    /// The program ID.
    program_id: N::ProgramID,
    /// The local commitments tree.
    local_commitments: LocalCommitments<N>,
}

impl<N: Network> VirtualMachine<N> {
    pub fn new(request: &Request<N>) -> Result<Self> {
        // Determine the caller.
        let caller = request.to_caller()?;

        // Compute the starting balance of the caller.
        let caller_balance = request
            .to_balance()
            .checked_sub(request.fee())
            .ok_or(VMError::BalanceInsufficient)?;

        // Initialize the balances.
        let balances = [(caller, caller_balance)].iter().cloned().collect();

        // Determine the program ID.
        let program_id = request.to_program_id()?;

        Ok(Self {
            request: request.clone(),
            caller,
            balances,
            program_id,
            local_commitments: LocalCommitments::new()?,
        })
    }

    #[cfg(test)]
    pub fn evaluate<R: Rng + CryptoRng>(mut self, rng: &mut R) -> Result<Response<N>> {
        // Compute the operation.
        let operation = self.request.operation().clone();
        match operation {
            Operation::Noop => (),
            Operation::Coinbase(recipient, amount) => self.coinbase(recipient, amount.0 as u64)?,
            Operation::Transfer(recipient, amount) => self.transfer(recipient, amount.0 as u64)?,
            Operation::Execute(..) => unimplemented!(),
        }

        self.build(rng)
    }

    pub fn execute<R: Rng + CryptoRng>(mut self, rng: &mut R) -> Result<Transaction<N>> {
        // Compute the operation.
        let operation = self.request.operation().clone();
        match operation {
            Operation::Noop => (),
            Operation::Coinbase(recipient, amount) => self.coinbase(recipient, amount.0 as u64)?,
            Operation::Transfer(recipient, amount) => self.transfer(recipient, amount.0 as u64)?,
            Operation::Execute(..) => unimplemented!(),
        }

        // Compute the transition.
        let response = self.build(rng)?;
        let transition = Transition::<N>::from(&self.request, &response, rng)?;

        Transaction::from(N::NETWORK_ID, *N::inner_circuit_id(), vec![transition])
    }

    /// Generates the given `amount` to `recipient`.
    fn coinbase(&mut self, recipient: Address<N>, amount: u64) -> Result<()> {
        let mut balances = self.balances.clone();

        // Increment the balance of the recipient.
        match balances.get_mut(&recipient) {
            Some(balance) => *balance = balance.checked_add(amount).ok_or(VMError::BalanceOverflow)?,
            None => {
                if balances.insert(recipient, amount).is_some() {
                    return Err(VMError::BalanceOverwritten.into());
                }
            }
        }

        self.balances = balances;

        Ok(())
    }

    /// Transfers the given `amount` from `caller` to `recipient`.
    fn transfer(&mut self, recipient: Address<N>, amount: u64) -> Result<()> {
        let mut balances = self.balances.clone();

        // Decrement the balance of the caller.
        match balances.get_mut(&self.caller) {
            Some(balance) => *balance = balance.checked_sub(amount).ok_or(VMError::BalanceInsufficient)?,
            None => return Err(VMError::MissingCaller(self.caller.to_string()).into()),
        }

        // Increment the balance of the recipient.
        match balances.get_mut(&recipient) {
            Some(balance) => *balance = balance.checked_add(amount).ok_or(VMError::BalanceOverflow)?,
            None => {
                if balances.insert(recipient, amount).is_some() {
                    return Err(VMError::BalanceOverwritten.into());
                }
            }
        }

        self.balances = balances;

        Ok(())
    }

    /// Returns a response based on the current state of the virtual machine.
    fn build<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<Response<N>> {
        assert_eq!(
            self.balances.len(),
            N::NUM_OUTPUT_RECORDS,
            "For now, only 2 outputs are support, this will change"
        );

        let serial_numbers = self.request.to_serial_numbers()?;

        let mut records = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        for (i, ((owner, balance), serial_number)) in self
            .balances
            .iter()
            .zip_eq(serial_numbers.iter())
            .take(N::NUM_OUTPUT_RECORDS)
            .enumerate()
        {
            let program_id = match i < self.request.function_type().output_count() as usize {
                true => self.program_id,
                false => *N::noop_program_id(),
            };

            records.push(Record::new_output(
                *owner,
                *balance,
                Default::default(),
                program_id,
                *serial_number,
                rng,
            )?);
        }

        Response::new(records, rng)
    }
}
