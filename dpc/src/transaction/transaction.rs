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
    DPCError,
    DPCScheme,
    LedgerProof,
    Memo,
    Network,
    OuterPublicVariables,
    RecordScheme,
    StateTransition,
    TransactionKernel,
    TransactionMetadata,
    ViewKey,
    DPC,
};
use snarkvm_algorithms::traits::SNARK;
use snarkvm_utilities::{has_duplicates, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
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
    /// The transaction metadata.
    metadata: TransactionMetadata<N>,
    /// The encrypted output records.
    encrypted_records: Vec<EncryptedRecord<N>>,
    #[derivative(PartialEq = "ignore")]
    /// Zero-knowledge proof attesting to the validity of the transaction.
    proof: <N::OuterSNARK as SNARK>::Proof,
}

impl<N: Network> Transaction<N> {
    /// Initializes a new coinbase transaction.
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        let transition = StateTransition::new_coinbase(recipient, amount, rng)?;
        let authorization = DPC::<N>::authorize(&vec![], &transition, rng)?;
        DPC::<N>::execute(authorization, transition.executable(), LedgerProof::default(), rng)
    }

    /// Initializes an instance of `Transaction` from the given inputs.
    pub fn from(
        kernel: TransactionKernel<N>,
        metadata: TransactionMetadata<N>,
        encrypted_records: Vec<EncryptedRecord<N>>,
        proof: <N::OuterSNARK as SNARK>::Proof,
    ) -> Result<Self> {
        assert!(kernel.is_valid());
        assert_eq!(N::NUM_OUTPUT_RECORDS, encrypted_records.len());

        let transaction = Self {
            kernel,
            metadata,
            encrypted_records,
            proof,
        };

        match transaction.is_valid() {
            true => Ok(transaction),
            false => Err(anyhow!("Failed to initialize a transaction")),
        }
    }

    /// Returns `true` if the transaction is well-formed, meaning it contains
    /// the correct network ID, unique serial numbers, unique commitments, and a valid proof.
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

        // Returns `false` if the number of encrypted records in the transaction is incorrect.
        if self.encrypted_records().len() != N::NUM_OUTPUT_RECORDS {
            eprintln!("Transaction contains incorrect number of encrypted records");
            return false;
        }

        // Returns `false` if the transaction proof is invalid.
        match N::OuterSNARK::verify(
            N::outer_circuit_verifying_key(),
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

    /// Returns the value balance.
    pub fn value_balance(&self) -> &AleoAmount {
        self.kernel.value_balance()
    }

    /// Returns the memo.
    pub fn memo(&self) -> &Memo<N> {
        self.kernel.memo()
    }

    /// Returns the block hash.
    pub fn block_hash(&self) -> N::BlockHash {
        self.metadata.block_hash()
    }

    /// Returns the inner circuit ID.
    pub fn inner_circuit_id(&self) -> &N::InnerCircuitID {
        self.metadata.inner_circuit_id()
    }

    /// Returns the encrypted records.
    pub fn encrypted_records(&self) -> &[EncryptedRecord<N>] {
        &self.encrypted_records
    }

    /// Returns a reference to the kernel of the transaction.
    pub fn kernel(&self) -> &TransactionKernel<N> {
        &self.kernel
    }

    /// Returns a reference to the metadata of the transaction.
    pub fn metadata(&self) -> &TransactionMetadata<N> {
        &self.metadata
    }

    /// Returns a reference to the proof of the transaction.
    pub fn proof(&self) -> &<N::OuterSNARK as SNARK>::Proof {
        &self.proof
    }

    /// Transaction ID = Hash(network ID || serial numbers || commitments || value balance || memo)
    pub fn to_transaction_id(&self) -> Result<N::TransactionID> {
        self.kernel.to_transaction_id()
    }

    /// Returns the encrypted record hashes.
    pub fn to_encrypted_record_ids(&self) -> Result<Vec<N::EncryptedRecordID>> {
        Ok(self
            .encrypted_records
            .iter()
            .take(N::NUM_OUTPUT_RECORDS)
            .map(|e| Ok(e.to_hash()?))
            .collect::<Result<Vec<_>>>()?)
    }

    /// Returns the records that can be decrypted with the given account view key.
    pub fn to_decrypted_records(&self, account_view_key: &ViewKey<N>) -> Option<Vec<Record<N>>> {
        self.encrypted_records
            .iter()
            .take(N::NUM_OUTPUT_RECORDS)
            .map(|e| e.decrypt(account_view_key))
            .filter(|decryption_result| match decryption_result {
                Ok(r) => !r.is_dummy(),
                Err(_) => true,
            })
            .collect::<Result<Vec<Record<N>>, DPCError>>()
            .ok()
    }
}

impl<N: Network> ToBytes for Transaction<N> {
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

impl<N: Network> FromBytes for Transaction<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the transaction kernel.
        let kernel = FromBytes::read_le(&mut reader)?;
        // Read the transaction metadata.
        let metadata = FromBytes::read_le(&mut reader)?;
        // Read the encrypted records.
        let mut encrypted_records = Vec::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            encrypted_records.push(FromBytes::read_le(&mut reader)?);
        }
        // Read the transaction proof.
        let proof: <N::OuterSNARK as SNARK>::Proof = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(kernel, metadata, encrypted_records, proof).expect("Failed to deserialize a transaction"))
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
            "Transaction {{ network_id: {:?}, serial_numbers: {:?}, commitments: {:?}, value_balance: {:?}, memo: {:?}, block_hash: {:?}, inner_circuit_id: {:?}, proof: {:?} }}",
            self.network_id(),
            self.serial_numbers(),
            self.commitments(),
            self.value_balance(),
            self.memo(),
            self.block_hash(),
            self.inner_circuit_id(),
            self.proof(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    use snarkvm_utilities::{FromBytes, UniformRand};

    use crate::{
        testnet2::Testnet2,
        Account,
        AccountScheme,
        AleoAmount,
        EncryptedRecord,
        Memo,
        Payload,
        Program,
        ProgramScheme,
        Record,
        TransactionKernel,
        TransactionMetadata,
        ViewKey,
        PAYLOAD_SIZE,
    };
    use snarkvm_algorithms::snark::groth16::Proof;
    use snarkvm_fields::{Fp256, Fp384};

    #[test]
    fn test_decrypt_records() {
        let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);
        let noop_program = Program::<Testnet2>::new_noop().unwrap();
        let dummy_account = Account::<Testnet2>::new(rng).unwrap();

        // Construct output records
        let mut payload = [0u8; PAYLOAD_SIZE];
        rng.fill(&mut payload);
        let record = Record::new_output(
            dummy_account.address(),
            1234,
            Payload::from_bytes_le(&payload).unwrap(),
            noop_program.program_id(),
            UniformRand::rand(rng),
            rng,
        )
        .unwrap();
        let dummy_record = Record::new_noop_output(dummy_account.address(), UniformRand::rand(rng), rng).unwrap();

        // Encrypt output records
        let (encrypted_record, _) = EncryptedRecord::encrypt(&record, rng).unwrap();
        let (encrypted_dummy_record, _) = EncryptedRecord::encrypt(&dummy_record, rng).unwrap();
        let account_view_key = ViewKey::from_private_key(&dummy_account.private_key()).unwrap();

        // Construct transaction with 1 output record and 1 dummy output record
        let transaction = Transaction::<Testnet2> {
            kernel: TransactionKernel::new(
                vec![Fp256::from(1u8), Fp256::from(2u8)],
                vec![Fp256::from(3u8), Fp256::from(4u8)],
                AleoAmount(1234),
                Memo::default(),
            )
            .unwrap(),
            metadata: TransactionMetadata::new(Fp256::from(1u8), Fp384::from(1u8)),
            encrypted_records: vec![encrypted_record, encrypted_dummy_record],
            proof: Proof::default(),
        };

        let decrypted_records = transaction.to_decrypted_records(&account_view_key).unwrap();
        assert_eq!(decrypted_records.len(), 1); // Excludes dummy record upon decryption
        assert_eq!(decrypted_records.first().unwrap(), &record);
    }
}
