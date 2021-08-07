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

use crate::{record::*, AleoAmount, Network, Parameters, TransactionError, TransactionKernel, TransactionScheme};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{SignatureScheme, SNARK},
};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use blake2::{digest::Digest, Blake2s as b2s};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "C: Parameters"),
    PartialEq(bound = "C: Parameters"),
    Eq(bound = "C: Parameters")
)]
pub struct Transaction<C: Parameters> {
    /// The network this transaction for.
    pub network: Network,
    /// The serial numbers of the input records.
    pub serial_numbers: Vec<<C::AccountSignatureScheme as SignatureScheme>::PublicKey>,
    /// The commitment of the output records.
    pub commitments: Vec<C::RecordCommitment>,
    /// A value balance is the difference between the input and output record values.
    /// The value balance serves as the transaction fee for the miner. Only coinbase transactions
    /// may possess a negative value balance representing tokens being minted.
    pub value_balance: AleoAmount,
    /// Publicly-visible data associated with the transaction.
    #[derivative(Default(value = "[0u8; 64]"))]
    pub memo: [u8; 64],
    /// The signatures that authorized the transaction kernel.
    pub signatures: Vec<<C::AccountSignatureScheme as SignatureScheme>::Signature>,
    /// The root of the ledger commitment tree.
    pub ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,
    /// The ID of the inner circuit used to execute this transaction.
    pub inner_circuit_id: C::InnerCircuitID,
    /// The encrypted output records.
    pub encrypted_records: Vec<EncryptedRecord<C>>,
    #[derivative(PartialEq = "ignore")]
    /// Zero-knowledge proof attesting to the validity of the transaction.
    pub proof: <C::OuterSNARK as SNARK>::Proof,
}

impl<C: Parameters> Transaction<C> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        network: Network,
        serial_numbers: Vec<<Self as TransactionScheme>::SerialNumber>,
        commitments: Vec<<Self as TransactionScheme>::Commitment>,
        value_balance: AleoAmount,
        memo: <Self as TransactionScheme>::Memo,
        ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters>,
        inner_circuit_id: C::InnerCircuitID,
        proof: <C::OuterSNARK as SNARK>::Proof,
        signatures: Vec<<C::AccountSignatureScheme as SignatureScheme>::Signature>,
        encrypted_records: Vec<EncryptedRecord<C>>,
    ) -> Self {
        assert_eq!(C::NUM_INPUT_RECORDS, serial_numbers.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, commitments.len());
        assert_eq!(C::NUM_INPUT_RECORDS, signatures.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, encrypted_records.len());

        Self {
            network,
            serial_numbers,
            commitments,
            memo,
            ledger_digest,
            inner_circuit_id,
            proof,
            value_balance,
            signatures,
            encrypted_records,
        }
    }

    /// Returns the kernel of the transaction.
    pub fn to_kernel(&self) -> TransactionKernel<C> {
        let kernel = TransactionKernel {
            network_id: self.network.id(),
            serial_numbers: self.serial_numbers.clone(),
            commitments: self.commitments.clone(),
            value_balance: self.value_balance,
            memo: self.memo,
        };
        debug_assert!(kernel.is_valid());
        kernel
    }

    /// Returns the encrypted record hashes.
    pub fn to_encrypted_record_hashes(&self) -> Result<Vec<C::EncryptedRecordDigest>> {
        assert_eq!(C::NUM_OUTPUT_RECORDS, self.encrypted_records.len());

        let mut encrypted_record_hashes = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for encrypted_record in self.encrypted_records.iter().take(C::NUM_OUTPUT_RECORDS) {
            encrypted_record_hashes.push(encrypted_record.to_hash()?);
        }

        Ok(encrypted_record_hashes)
    }
}

impl<C: Parameters> TransactionScheme for Transaction<C> {
    type Commitment = C::RecordCommitment;
    type Digest = MerkleTreeDigest<C::RecordCommitmentTreeParameters>;
    type EncryptedRecord = EncryptedRecord<C>;
    type InnerCircuitID = C::InnerCircuitID;
    type Memo = [u8; 64];
    type SerialNumber = <C::AccountSignatureScheme as SignatureScheme>::PublicKey;
    type Signature = <C::AccountSignatureScheme as SignatureScheme>::Signature;
    type ValueBalance = AleoAmount;

    /// Transaction id = Hash of (serial numbers || commitments || memo)
    fn transaction_id(&self) -> Result<[u8; 32], TransactionError> {
        let mut pre_image_bytes: Vec<u8> = vec![];

        for serial_number in self.serial_numbers() {
            pre_image_bytes.extend(&serial_number.to_bytes_le()?);
        }

        for commitment in self.commitments() {
            pre_image_bytes.extend(&commitment.to_bytes_le()?);
        }

        pre_image_bytes.extend(self.memo());

        let mut h = b2s::new();
        h.update(&pre_image_bytes);

        let mut result = [0u8; 32];
        result.copy_from_slice(&h.finalize());
        Ok(result)
    }

    fn network_id(&self) -> u8 {
        self.network.id()
    }

    fn serial_numbers(&self) -> &[Self::SerialNumber] {
        self.serial_numbers.as_slice()
    }

    fn commitments(&self) -> &[Self::Commitment] {
        self.commitments.as_slice()
    }

    fn value_balance(&self) -> Self::ValueBalance {
        self.value_balance
    }

    fn memo(&self) -> &Self::Memo {
        &self.memo
    }

    fn signatures(&self) -> &[Self::Signature] {
        &self.signatures
    }

    fn ledger_digest(&self) -> &Self::Digest {
        &self.ledger_digest
    }

    fn inner_circuit_id(&self) -> &Self::InnerCircuitID {
        &self.inner_circuit_id
    }

    fn encrypted_records(&self) -> &[Self::EncryptedRecord] {
        &self.encrypted_records
    }
}

impl<C: Parameters> ToBytes for Transaction<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.network.write_le(&mut writer)?;
        self.serial_numbers.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        self.memo.write_le(&mut writer)?;

        for signature in &self.signatures {
            signature.write_le(&mut writer)?;
        }

        self.ledger_digest.write_le(&mut writer)?;
        self.inner_circuit_id.write_le(&mut writer)?;

        for encrypted_record in &self.encrypted_records {
            encrypted_record.write_le(&mut writer)?;
        }

        self.proof.write_le(&mut writer)
    }
}

impl<C: Parameters> FromBytes for Transaction<C> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the network ID.
        let network: Network = FromBytes::read_le(&mut reader)?;

        // Read the serial numbers.
        let mut serial_numbers = Vec::with_capacity(C::NUM_INPUT_RECORDS);
        for _ in 0..C::NUM_INPUT_RECORDS {
            serial_numbers.push(FromBytes::read_le(&mut reader)?);
        }

        // Read the commitments
        let mut commitments = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance: AleoAmount = FromBytes::read_le(&mut reader)?;
        let memo: <Self as TransactionScheme>::Memo = FromBytes::read_le(&mut reader)?;

        // Read the signatures
        let mut signatures = Vec::with_capacity(C::NUM_INPUT_RECORDS);
        for _ in 0..C::NUM_INPUT_RECORDS {
            signatures.push(FromBytes::read_le(&mut reader)?);
        }

        let ledger_digest: MerkleTreeDigest<C::RecordCommitmentTreeParameters> = FromBytes::read_le(&mut reader)?;
        let inner_circuit_id: C::InnerCircuitID = FromBytes::read_le(&mut reader)?;

        // Read the encrypted records.
        let mut encrypted_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            encrypted_records.push(FromBytes::read_le(&mut reader)?);
        }

        let proof: <C::OuterSNARK as SNARK>::Proof = FromBytes::read_le(&mut reader)?;

        Ok(Self {
            network,
            serial_numbers,
            commitments,
            value_balance,
            memo,
            signatures,
            ledger_digest,
            inner_circuit_id,
            encrypted_records,
            proof,
        })
    }
}

// TODO add debug support for record ciphertexts
impl<C: Parameters> fmt::Debug for Transaction<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Transaction {{ network_id: {:?}, serial_numbers: {:?}, commitments: {:?}, value_balance: {:?}, memo: {:?}, signatures: {:?}, digest: {:?}, inner_circuit_id: {:?}, proof: {:?} }}",
            self.network,
            self.serial_numbers,
            self.commitments,
            self.value_balance,
            self.memo,
            self.signatures,
            self.ledger_digest,
            self.inner_circuit_id,
            self.proof,
        )
    }
}
