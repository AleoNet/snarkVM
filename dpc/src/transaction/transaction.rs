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
    AleoAmount,
    Memo,
    OuterPublicVariables,
    Parameters,
    TransactionKernel,
    TransactionMetadata,
    TransactionScheme,
};
use snarkvm_algorithms::{
    merkle_tree::MerkleTreeDigest,
    traits::{CRH, SNARK},
};
use snarkvm_utilities::{has_duplicates, FromBytes, ToBytes};

use anyhow::Result;
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
    /// The transaction kernel.
    kernel: TransactionKernel<C>,
    /// The transaction metadata.
    metadata: TransactionMetadata<C>,
    /// The encrypted output records.
    encrypted_records: Vec<EncryptedRecord<C>>,
    #[derivative(PartialEq = "ignore")]
    /// Zero-knowledge proof attesting to the validity of the transaction.
    proof: <C::OuterSNARK as SNARK>::Proof,
}

impl<C: Parameters> Transaction<C> {
    /// Initializes an instance of `Transaction` from the given inputs.
    pub fn from(
        kernel: TransactionKernel<C>,
        metadata: TransactionMetadata<C>,
        encrypted_records: Vec<EncryptedRecord<C>>,
        proof: <C::OuterSNARK as SNARK>::Proof,
    ) -> Self {
        assert!(kernel.is_valid());
        assert_eq!(C::NUM_OUTPUT_RECORDS, encrypted_records.len());

        Self {
            kernel,
            metadata,
            encrypted_records,
            proof,
        }
    }

    /// Returns `true` if the transaction is well-formed, meaning it contains
    /// the correct network ID, unique serial numbers, unique commitments, and a valid proof.
    pub fn is_valid(&self) -> bool {
        // Returns `false` if the number of serial numbers in the transaction is incorrect.
        if self.serial_numbers().len() != C::NUM_INPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of serial numbers");
            return false;
        }

        // Returns `false` if there are duplicate serial numbers in the transaction.
        if has_duplicates(self.serial_numbers().iter()) {
            eprintln!("Transaction contains duplicate serial numbers");
            return false;
        }

        // Returns `false` if the number of commitments in the transaction is incorrect.
        if self.commitments().len() != C::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of commitments");
            return false;
        }

        // Returns `false` if there are duplicate commitments numbers in the transaction.
        if has_duplicates(self.commitments().iter()) {
            eprintln!("Transaction contains duplicate commitments");
            return false;
        }

        // Returns `false` if the number of encrypted records in the transaction is incorrect.
        if self.encrypted_records().len() != C::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of encrypted records");
            return false;
        }

        // Returns `false` if the transaction proof is invalid.
        match C::OuterSNARK::verify(
            C::outer_circuit_verifying_key(),
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

    /// Returns a reference to the kernel of the transaction.
    pub fn kernel(&self) -> &TransactionKernel<C> {
        &self.kernel
    }

    /// Returns a reference to the metadata of the transaction.
    pub fn metadata(&self) -> &TransactionMetadata<C> {
        &self.metadata
    }

    /// Returns a reference to the proof of the transaction.
    pub fn proof(&self) -> &<C::OuterSNARK as SNARK>::Proof {
        &self.proof
    }

    /// Returns the encrypted record hashes.
    pub fn to_encrypted_record_hashes(&self) -> Result<Vec<C::EncryptedRecordDigest>> {
        Ok(self
            .encrypted_records
            .iter()
            .take(C::NUM_OUTPUT_RECORDS)
            .map(|e| Ok(e.to_hash()?))
            .collect::<Result<Vec<_>>>()?)
    }
}

impl<C: Parameters> TransactionScheme<C> for Transaction<C> {
    type Digest = MerkleTreeDigest<C::LedgerCommitmentsTreeParameters>;
    type EncryptedRecord = EncryptedRecord<C>;

    fn network_id(&self) -> u16 {
        self.kernel.network_id()
    }

    fn serial_numbers(&self) -> &[C::SerialNumber] {
        self.kernel.serial_numbers()
    }

    fn commitments(&self) -> &[C::RecordCommitment] {
        self.kernel.commitments()
    }

    fn value_balance(&self) -> &AleoAmount {
        self.kernel.value_balance()
    }

    fn memo(&self) -> &Memo<C> {
        self.kernel.memo()
    }

    fn ledger_digest(&self) -> &Self::Digest {
        self.metadata.ledger_digest()
    }

    fn inner_circuit_id(&self) -> &C::InnerCircuitID {
        self.metadata.inner_circuit_id()
    }

    fn encrypted_records(&self) -> &[Self::EncryptedRecord] {
        &self.encrypted_records
    }

    /// Transaction ID = Hash(network ID || serial numbers || commitments || value balance || memo)
    fn to_transaction_id(&self) -> Result<C::TransactionID> {
        Ok(C::transaction_id_crh().hash(&self.kernel().to_bytes_le()?)?)
    }
}

impl<C: Parameters> ToBytes for Transaction<C> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.kernel().write_le(&mut writer)?;
        self.metadata().write_le(&mut writer)?;
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
        let kernel = FromBytes::read_le(&mut reader)?;
        // Read the transaction metadata.
        let metadata = FromBytes::read_le(&mut reader)?;
        // Read the encrypted records.
        let mut encrypted_records = Vec::with_capacity(C::NUM_OUTPUT_RECORDS);
        for _ in 0..C::NUM_OUTPUT_RECORDS {
            encrypted_records.push(FromBytes::read_le(&mut reader)?);
        }
        // Read the transaction proof.
        let proof: <C::OuterSNARK as SNARK>::Proof = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(kernel, metadata, encrypted_records, proof))
    }
}

// TODO add debug support for record ciphertexts
impl<C: Parameters> fmt::Debug for Transaction<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Transaction {{ network_id: {:?}, serial_numbers: {:?}, commitments: {:?}, value_balance: {:?}, memo: {:?}, digest: {:?}, inner_circuit_id: {:?}, proof: {:?} }}",
            self.network_id(),
            self.serial_numbers(),
            self.commitments(),
            self.value_balance(),
            self.memo(),
            self.ledger_digest(),
            self.inner_circuit_id(),
            self.proof(),
        )
    }
}
