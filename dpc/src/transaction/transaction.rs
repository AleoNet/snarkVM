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

use crate::{
    record::*,
    Address,
    AleoAmount,
    LedgerProof,
    Memo,
    Network,
    OuterPublicVariables,
    StateTransition,
    TransactionKernel,
    DPC,
};
use snarkvm_algorithms::traits::SNARK;
use snarkvm_utilities::{has_duplicates, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use rand::{CryptoRng, Rng};
use std::{
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
    /// The transaction kernel.
    kernel: TransactionKernel<N>,
    /// The block hash used for the ledger inclusion proof.
    block_hash: N::BlockHash,
    /// The ID of the inner circuit used to execute this transaction.
    inner_circuit_id: N::InnerCircuitID,
    /// The ciphertexts of the output records.
    ciphertexts: Vec<RecordCiphertext<N>>,
    /// Publicly-visible data associated with the transaction.
    memo: Memo<N>,
    #[derivative(PartialEq = "ignore")]
    /// Zero-knowledge proof attesting to the validity of the transaction.
    proof: <N::OuterSNARK as SNARK>::Proof,
}

impl<N: Network> Transaction<N> {
    /// Initializes a new coinbase transaction.
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        let transition = StateTransition::new_coinbase(recipient, amount, rng)?;
        let signatures = DPC::<N>::authorize(&vec![], &transition, rng)?;
        DPC::<N>::execute(signatures, &transition, LedgerProof::default(), rng)
    }

    /// Initializes an instance of `Transaction` from the given inputs.
    pub fn from(
        kernel: TransactionKernel<N>,
        block_hash: N::BlockHash,
        inner_circuit_id: N::InnerCircuitID,
        ciphertexts: Vec<RecordCiphertext<N>>,
        memo: Memo<N>,
        proof: <N::OuterSNARK as SNARK>::Proof,
    ) -> Result<Self> {
        assert!(kernel.is_valid());
        assert_eq!(N::NUM_OUTPUT_RECORDS, ciphertexts.len());

        let transaction = Self {
            kernel,
            block_hash,
            inner_circuit_id,
            ciphertexts,
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
    pub fn is_valid(&self) -> bool {
        // Returns `false` if the number of serial numbers in the transaction is incorrect.
        if self.serial_numbers().len() != N::NUM_INPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of serial numbers");
            return false;
        }

        // Returns `false` if there are duplicate serial numbers in the transaction.
        if has_duplicates(self.serial_numbers().iter()) {
            eprintln!("Transaction contains duplicate serial numbers");
            return false;
        }

        // Returns `false` if the number of commitments in the transaction is incorrect.
        if self.commitments().len() != N::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of commitments");
            return false;
        }

        // Returns `false` if there are duplicate commitments numbers in the transaction.
        if has_duplicates(self.commitments().iter()) {
            eprintln!("Transaction contains duplicate commitments");
            return false;
        }

        // Returns `false` if the number of record ciphertexts in the transaction is incorrect.
        if self.ciphertext_ids().len() != N::NUM_OUTPUT_RECORDS || self.ciphertexts().len() != N::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of record ciphertexts");
            return false;
        }

        // Returns `false` if the record ciphertexts do not match their corresponding ids.
        for (ciphertext_id, ciphertext) in self.ciphertext_ids().iter().zip_eq(self.ciphertexts().iter()) {
            match ciphertext.to_hash() {
                Ok(id) => {
                    if id != *ciphertext_id {
                        eprintln!("Transaction contains mismatching ciphertext and ciphertext ID");
                        return false;
                    }
                }
                Err(error) => {
                    eprintln!("Unable to construct the record ciphertext ID - {}", error);
                    return false;
                }
            }
        }

        // Returns `false` if the transaction proof is invalid.
        match N::OuterSNARK::verify(
            N::outer_verifying_key(),
            &match OuterPublicVariables::from(&self) {
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
    pub fn network_id(&self) -> u16 {
        self.kernel.network_id()
    }

    /// Returns the serial numbers.
    pub fn serial_numbers(&self) -> &[N::SerialNumber] {
        self.kernel.serial_numbers()
    }

    /// Returns the commitments.
    pub fn commitments(&self) -> &[N::Commitment] {
        self.kernel.commitments()
    }

    /// Returns the ciphertext IDs.
    pub fn ciphertext_ids(&self) -> &[N::CiphertextID] {
        self.kernel.ciphertext_ids()
    }

    /// Returns the value balance.
    pub fn value_balance(&self) -> &AleoAmount {
        self.kernel.value_balance()
    }

    /// Returns the block hash.
    pub fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the inner circuit ID.
    pub fn inner_circuit_id(&self) -> N::InnerCircuitID {
        self.inner_circuit_id
    }

    /// Returns a reference to the kernel of the transaction.
    pub fn kernel(&self) -> &TransactionKernel<N> {
        &self.kernel
    }

    /// Returns the output record ciphertexts.
    pub fn ciphertexts(&self) -> &[RecordCiphertext<N>] {
        &self.ciphertexts
    }

    /// Returns a reference to the memo.
    pub fn memo(&self) -> &Memo<N> {
        &self.memo
    }

    /// Returns a reference to the proof of the transaction.
    pub fn proof(&self) -> &<N::OuterSNARK as SNARK>::Proof {
        &self.proof
    }

    /// Transaction ID = Hash(network ID || serial numbers || commitments || ciphertext_ids || value balance)
    pub fn to_transaction_id(&self) -> Result<N::TransactionID> {
        self.kernel.to_transaction_id()
    }
}

impl<N: Network> ToBytes for Transaction<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.kernel().write_le(&mut writer)?;
        self.block_hash.write_le(&mut writer)?;
        self.inner_circuit_id.write_le(&mut writer)?;
        for encrypted_record in &self.ciphertexts {
            encrypted_record.write_le(&mut writer)?;
        }
        self.memo.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Transaction<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the transaction kernel.
        let kernel = FromBytes::read_le(&mut reader)?;
        // Read the transaction metadata.
        let block_hash = FromBytes::read_le(&mut reader)?;
        let inner_circuit_id = FromBytes::read_le(&mut reader)?;
        // Read the encrypted records.
        let mut ciphertexts = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            ciphertexts.push(FromBytes::read_le(&mut reader)?);
        }
        // Read the transaction memo.
        let memo: Memo<N> = FromBytes::read_le(&mut reader)?;
        // Read the transaction proof.
        let proof: <N::OuterSNARK as SNARK>::Proof = FromBytes::read_le(&mut reader)?;

        Ok(
            Self::from(kernel, block_hash, inner_circuit_id, ciphertexts, memo, proof)
                .expect("Failed to deserialize a transaction"),
        )
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
            "Transaction {{ network_id: {:?}, serial_numbers: {:?}, commitments: {:?}, ciphertext_ids: {:?}, value_balance: {:?}, block_hash: {:?}, inner_circuit_id: {:?},  memo: {:?}, proof: {:?} }}",
            self.network_id(),
            self.serial_numbers(),
            self.commitments(),
            self.ciphertext_ids(),
            self.value_balance(),
            self.block_hash(),
            self.inner_circuit_id(),
            self.memo(),
            self.proof(),
        )
    }
}
