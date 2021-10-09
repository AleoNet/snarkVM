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

use crate::{record::*, Address, AleoAmount, LedgerProof, Memo, Network, Transition};
use snarkvm_algorithms::CRH;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use rand::{CryptoRng, Rng};
use std::{
    collections::HashSet,
    fmt,
    hash::{Hash, Hasher},
    io::{Read, Result as IoResult, Write},
};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Transaction<N: Network> {
    /// The network ID.
    network_id: u16,
    /// The state transition.
    transition: Transition<N>,
    /// The ID of the inner circuit used to execute this transaction.
    inner_circuit_id: N::InnerCircuitID,
    /// Publicly-visible data associated with the transaction.
    memo: Memo<N>,
}

impl<N: Network> Transaction<N> {
    /// Initializes a new coinbase transaction.
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        State::new_coinbase(recipient, amount, rng)?.execute(LedgerProof::default(), rng)
    }

    /// Initializes an instance of `Transaction` from the given inputs.
    pub fn from(
        network_id: u16,
        transition: Transition<N>,
        inner_circuit_id: N::InnerCircuitID,
        memo: Memo<N>,
    ) -> Result<Self> {
        let transaction = Self {
            network_id,
            transition,
            inner_circuit_id,
            memo,
        };

        match transaction.is_valid() {
            true => Ok(transaction),
            false => Err(anyhow!("Failed to initialize a transaction")),
        }
    }

    /// Returns `true` if the transaction is well-formed, meaning it contains
    /// the correct network ID, unique serial numbers, unique commitments,
    /// correct ciphertext IDs, and a valid proof.
    pub fn is_valid(&self) -> bool {
        // Returns `false` if the network ID is incorrect.
        if self.network_id != N::NETWORK_ID {
            eprintln!("Transaction contains an incorrect network ID");
            return false;
        }

        // Returns `false` if the transition is not well-formed.
        if !self.transition.is_valid(self.inner_circuit_id) {
            eprintln!("Transition contains a transition that is not well-formed");
            return false;
        }

        true
    }

    /// Returns the network ID.
    pub fn network_id(&self) -> u16 {
        self.network_id
    }

    /// Returns the serial numbers.
    pub fn serial_numbers(&self) -> &[N::SerialNumber] {
        self.transition.serial_numbers()
    }

    /// Returns the commitments.
    pub fn commitments(&self) -> &[N::Commitment] {
        self.transition.commitments()
    }

    /// Returns the output record ciphertexts.
    pub fn ciphertexts(&self) -> &[RecordCiphertext<N>] {
        &self.transition.ciphertexts()
    }

    /// Returns the value balance.
    pub fn value_balance(&self) -> &AleoAmount {
        self.transition.value_balance()
    }

    /// Returns the inner circuit ID.
    pub fn inner_circuit_id(&self) -> N::InnerCircuitID {
        self.inner_circuit_id
    }

    /// Returns a reference to the state transition.
    pub fn transition(&self) -> &Transition<N> {
        &self.transition
    }

    /// Returns a reference to the memo.
    pub fn memo(&self) -> &Memo<N> {
        &self.memo
    }

    /// Returns the block hashes used to execute the transitions.
    pub fn block_hashes(&self) -> HashSet<N::BlockHash> {
        [self.transition.block_hash()].iter().cloned().collect()
    }

    /// Returns the ciphertext IDs.
    pub fn to_ciphertext_ids(&self) -> Result<Vec<N::CiphertextID>> {
        self.transition.to_ciphertext_ids()
    }

    /// Returns the transaction ID.
    pub fn to_transaction_id(&self) -> Result<N::TransactionID> {
        Ok(N::transaction_id_crh().hash(&to_bytes_le![self.transition.to_transition_id()?]?)?)
    }
}

impl<N: Network> ToBytes for Transaction<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.network_id.write_le(&mut writer)?;
        self.transition.write_le(&mut writer)?;
        self.inner_circuit_id.write_le(&mut writer)?;
        self.memo.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Transaction<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the network ID.
        let network_id: u16 = FromBytes::read_le(&mut reader)?;
        // Read the transition.
        let transition = FromBytes::read_le(&mut reader)?;
        // Read the transaction metadata.
        let inner_circuit_id = FromBytes::read_le(&mut reader)?;
        // Read the transaction memo.
        let memo: Memo<N> = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(network_id, transition, inner_circuit_id, memo).expect("Failed to deserialize a transaction"))
    }
}

impl<N: Network> Hash for Transaction<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_transaction_id()
            .expect("Failed to compute the transaction ID")
            .hash(state);
    }
}

// TODO add debug support for record ciphertexts
impl<N: Network> fmt::Debug for Transaction<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Transaction {{ network_id: {:?}, inner_circuit_id: {:?}, transition: {:?}, memo: {:?} }}",
            self.network_id(),
            self.inner_circuit_id(),
            self.transition(),
            self.memo(),
        )
    }
}
