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

use crate::{record::*, AleoAmount, Network, Parameters, TransactionKernel, TransactionScheme};
use snarkvm_algorithms::{
    crh::BHPCompressedCRH,
    merkle_tree::MerkleTreeDigest,
    traits::{CRH, SNARK},
};
use snarkvm_curves::edwards_bls12::EdwardsProjective as EdwardsBls;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use once_cell::sync::Lazy;
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
    sync::Arc,
};

// TODO (raychu86): Derive EdwardsBls from <C: Parameters>
pub type TransactionIdCRH = BHPCompressedCRH<EdwardsBls, 26, 62>;

/// Lazily evaluated TransactionId CRH
pub static TRANSACTION_ID_CRH: Lazy<Arc<TransactionIdCRH>> =
    Lazy::new(|| Arc::new(TransactionIdCRH::setup("TransactionIdCRH")));

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
    pub serial_numbers: Vec<C::SerialNumber>,
    /// The commitment of the output records.
    pub commitments: Vec<C::RecordCommitment>,
    /// A value balance is the difference between the input and output record values.
    /// The value balance serves as the transaction fee for the miner. Only coinbase transactions
    /// may possess a negative value balance representing tokens being minted.
    pub value_balance: AleoAmount,
    /// Publicly-visible data associated with the transaction.
    #[derivative(Default(value = "[0u8; 64]"))]
    pub memo: [u8; 64],
    /// The root of the ledger commitment tree.
    pub ledger_digest: MerkleTreeDigest<C::LedgerCommitmentsTreeParameters>,
    /// The ID of the inner circuit used to execute this transaction.
    pub inner_circuit_id: C::InnerCircuitID,
    /// The encrypted output records.
    pub encrypted_records: Vec<EncryptedRecord<C>>,
    #[derivative(PartialEq = "ignore")]
    /// Zero-knowledge proof attesting to the validity of the transaction.
    pub proof: <C::OuterSNARK as SNARK>::Proof,
}

impl<C: Parameters> Transaction<C> {
    /// Initializes a new instance of `Transaction` from the given inputs.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        network: Network,
        serial_numbers: Vec<<Self as TransactionScheme>::SerialNumber>,
        commitments: Vec<<Self as TransactionScheme>::Commitment>,
        value_balance: AleoAmount,
        memo: <Self as TransactionScheme>::Memo,
        ledger_digest: MerkleTreeDigest<C::LedgerCommitmentsTreeParameters>,
        inner_circuit_id: C::InnerCircuitID,
        encrypted_records: Vec<EncryptedRecord<C>>,
        proof: <C::OuterSNARK as SNARK>::Proof,
    ) -> Self {
        assert_eq!(C::NUM_INPUT_RECORDS, serial_numbers.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, commitments.len());
        assert_eq!(C::NUM_OUTPUT_RECORDS, encrypted_records.len());

        Self {
            network,
            serial_numbers,
            commitments,
            value_balance,
            memo,
            ledger_digest,
            inner_circuit_id,
            encrypted_records,
            proof,
        }
    }

    /// Initializes an instance of `Transaction` from the given inputs.
    pub fn from(
        kernel: TransactionKernel<C>,
        ledger_digest: MerkleTreeDigest<C::LedgerCommitmentsTreeParameters>,
        inner_circuit_id: C::InnerCircuitID,
        encrypted_records: Vec<EncryptedRecord<C>>,
        proof: <C::OuterSNARK as SNARK>::Proof,
    ) -> Self {
        let TransactionKernel {
            network_id,
            serial_numbers,
            commitments,
            value_balance,
            memo,
        } = kernel;

        Self::new(
            Network::from_id(network_id),
            serial_numbers,
            commitments,
            value_balance,
            memo,
            ledger_digest,
            inner_circuit_id,
            encrypted_records,
            proof,
        )
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
    type Digest = MerkleTreeDigest<C::LedgerCommitmentsTreeParameters>;
    type EncryptedRecord = EncryptedRecord<C>;
    type InnerCircuitID = C::InnerCircuitID;
    type Memo = [u8; 64];
    type SerialNumber = C::SerialNumber;
    type Signature = C::AccountSignature;
    type ValueBalance = AleoAmount;

    /// Transaction ID = Hash(network ID || serial numbers || commitments || value balance || memo)
    fn transaction_id(&self) -> Result<[u8; 32]> {
        let serialized = &self.to_kernel().to_bytes_le()?;
        let hash_bytes = TRANSACTION_ID_CRH.hash(&serialized)?.to_bytes_le()?;

        assert_eq!(hash_bytes.len(), 32);

        let mut transaction_id = [0u8; 32];
        transaction_id.copy_from_slice(&hash_bytes);

        Ok(transaction_id)
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
        self.to_kernel().write_le(&mut writer)?;

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
        // Read the transaction kernel.
        let kernel: TransactionKernel<C> = FromBytes::read_le(&mut reader)?;

        let ledger_digest: MerkleTreeDigest<C::LedgerCommitmentsTreeParameters> = FromBytes::read_le(&mut reader)?;
        let inner_circuit_id: C::InnerCircuitID = FromBytes::read_le(&mut reader)?;

        // Read the encrypted records.
        let mut encrypted_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            encrypted_records.push(FromBytes::read_le(&mut reader)?);
        }

        let proof: <C::OuterSNARK as SNARK>::Proof = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(
            kernel,
            ledger_digest,
            inner_circuit_id,
            encrypted_records,
            proof,
        ))
    }
}

// TODO add debug support for record ciphertexts
impl<C: Parameters> fmt::Debug for Transaction<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Transaction {{ network_id: {:?}, serial_numbers: {:?}, commitments: {:?}, value_balance: {:?}, memo: {:?}, digest: {:?}, inner_circuit_id: {:?}, proof: {:?} }}",
            self.network,
            self.serial_numbers,
            self.commitments,
            self.value_balance,
            self.memo,
            self.ledger_digest,
            self.inner_circuit_id,
            self.proof,
        )
    }
}
