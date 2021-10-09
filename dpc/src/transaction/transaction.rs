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

use crate::{record::*, Address, AleoAmount, Memo, Network, OuterPublicVariables, Request, Transition, VirtualMachine};
use snarkvm_algorithms::{CRH, SNARK};
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
    /// The ID of the inner circuit used to execute this transaction.
    inner_circuit_id: N::InnerCircuitID,
    /// The state transition.
    transition: Transition<N>,
    /// Publicly-visible data associated with the transaction.
    memo: Memo<N>,
    #[derivative(PartialEq = "ignore")]
    /// The zero-knowledge proof attesting to the validity of the transition.
    proof: <N::OuterSNARK as SNARK>::Proof,
}

impl<N: Network> Transaction<N> {
    /// Initializes a new coinbase transaction.
    #[inline]
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        let request = Request::new_coinbase(recipient, amount, rng)?;
        VirtualMachine::<N>::new(&request)?.execute(rng)
    }

    /// Initializes an instance of `Transaction` from the given inputs.
    #[inline]
    pub fn from(
        network_id: u16,
        inner_circuit_id: N::InnerCircuitID,
        transition: Transition<N>,
        memo: Memo<N>,
        proof: <N::OuterSNARK as SNARK>::Proof,
    ) -> Result<Self> {
        let transaction = Self {
            network_id,
            transition,
            inner_circuit_id,
            memo,
            proof,
        };

        match transaction.is_valid() {
            true => Ok(transaction),
            false => Err(anyhow!("Failed to initialize a transaction")),
        }
    }

    /// Returns `true` if the transaction is well-formed, meaning it contains
    /// the correct network ID, unique serial numbers, unique commitments,
    /// correct ciphertext IDs, and a valid proof.
    #[inline]
    pub fn is_valid(&self) -> bool {
        // Returns `false` if the network ID is incorrect.
        if self.network_id != N::NETWORK_ID {
            eprintln!("Transaction contains an incorrect network ID");
            return false;
        }

        // Returns `false` if the transition is not well-formed.
        if !self.transition.is_valid() {
            eprintln!("Transition contains a transition that is not well-formed");
            return false;
        }

        // Returns `false` if the transition proof is invalid.
        match N::OuterSNARK::verify(
            N::outer_verifying_key(),
            &match OuterPublicVariables::from(&self.transition, self.inner_circuit_id) {
                Ok(outer_public_variables) => outer_public_variables,
                Err(error) => {
                    eprintln!("Unable to construct outer public variables - {}", error);
                    return false;
                }
            },
            self.proof(),
        ) {
            Ok(is_valid) => match is_valid {
                true => true,
                false => {
                    eprintln!("Transaction proof failed to verify");
                    false
                }
            },
            Err(error) => {
                eprintln!("Failed to validate transaction proof: {:?}", error);
                false
            }
        }
    }

    /// Returns the network ID.
    #[inline]
    pub fn network_id(&self) -> u16 {
        self.network_id
    }

    /// Returns the serial numbers.
    #[inline]
    pub fn serial_numbers(&self) -> &[N::SerialNumber] {
        self.transition.serial_numbers()
    }

    /// Returns the commitments.
    #[inline]
    pub fn commitments(&self) -> &[N::Commitment] {
        self.transition.commitments()
    }

    /// Returns the output record ciphertexts.
    #[inline]
    pub fn ciphertexts(&self) -> &[RecordCiphertext<N>] {
        &self.transition.ciphertexts()
    }

    /// Returns the value balance.
    #[inline]
    pub fn value_balance(&self) -> &AleoAmount {
        self.transition.value_balance()
    }

    /// Returns the inner circuit ID.
    #[inline]
    pub fn inner_circuit_id(&self) -> N::InnerCircuitID {
        self.inner_circuit_id
    }

    /// Returns a reference to the state transition.
    #[inline]
    pub fn transition(&self) -> &Transition<N> {
        &self.transition
    }

    /// Returns a reference to the memo.
    #[inline]
    pub fn memo(&self) -> &Memo<N> {
        &self.memo
    }

    /// Returns a reference to the proof of the transaction.
    #[inline]
    pub(crate) fn proof(&self) -> &<N::OuterSNARK as SNARK>::Proof {
        &self.proof
    }

    /// Returns the block hashes used to execute the transitions.
    #[inline]
    pub fn block_hashes(&self) -> HashSet<N::BlockHash> {
        [self.transition.block_hash()].iter().cloned().collect()
    }

    /// Returns the ciphertext IDs.
    #[inline]
    pub fn to_ciphertext_ids(&self) -> Result<Vec<N::CiphertextID>> {
        self.transition.to_ciphertext_ids()
    }

    /// Returns the transaction ID.
    #[inline]
    pub fn to_transaction_id(&self) -> Result<N::TransactionID> {
        Ok(N::transaction_id_crh().hash(&to_bytes_le![self.transition.to_transition_id()?]?)?)
    }
}

impl<N: Network> ToBytes for Transaction<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.network_id.write_le(&mut writer)?;
        self.inner_circuit_id.write_le(&mut writer)?;
        self.transition.write_le(&mut writer)?;
        self.memo.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Transaction<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let network_id: u16 = FromBytes::read_le(&mut reader)?;
        let inner_circuit_id = FromBytes::read_le(&mut reader)?;
        let transition = FromBytes::read_le(&mut reader)?;
        let memo: Memo<N> = FromBytes::read_le(&mut reader)?;
        let proof: <N::OuterSNARK as SNARK>::Proof = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(network_id, inner_circuit_id, transition, memo, proof)
            .expect("Failed to deserialize a transaction"))
    }
}

impl<N: Network> Hash for Transaction<N> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_transaction_id()
            .expect("Failed to compute the transaction ID")
            .hash(state);
    }
}

// TODO add debug support for record ciphertexts
impl<N: Network> fmt::Debug for Transaction<N> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Transaction {{ network_id: {:?}, inner_circuit_id: {:?}, transition: {:?}, memo: {:?}, proof: {:?} }}",
            self.network_id(),
            self.inner_circuit_id(),
            self.transition(),
            self.memo(),
            self.proof()
        )
    }
}
