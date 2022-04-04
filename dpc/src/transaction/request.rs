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

use crate::{Address, AleoAmount, ComputeKey, LedgerProof, Network, Operation, PrivateKey, Record};
use snarkvm_algorithms::SignatureScheme;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBits, ToBytes};

use anyhow::{anyhow, Result};
use itertools::Itertools;
use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use std::{
    collections::HashSet,
    fmt,
    io::{Read, Result as IoResult, Write},
};

// TODO (raychu86): Refactor this. Map records, ledger_proofs, and signatures together.
#[derive(Clone, Debug)]
pub struct Request<N: Network> {
    /// The records being consumed.
    records: Vec<Record<N>>,
    /// The inclusion proofs of ledger-consumed records.
    ledger_proofs: Vec<LedgerProof<N>>,
    /// The operation being performed.
    operation: Operation<N>,
    /// The network fee being paid.
    fee: AleoAmount,
    /// The signatures for the request (each record will have one).
    signatures: Vec<N::AccountSignature>,
    /// The visibility of the operation.
    is_public: bool,
}

impl<N: Network> Request<N> {
    /// Initializes a new coinbase generation.
    pub fn new_coinbase<R: Rng + CryptoRng>(
        recipient: Address<N>,
        amount: AleoAmount,
        is_public: bool,
        rng: &mut R,
    ) -> Result<Self> {
        let burner = PrivateKey::new(rng);
        let operation = Operation::Coinbase(recipient, amount);
        let fee = AleoAmount::ZERO.sub(amount);
        Self::new(&burner, vec![], vec![], operation, fee, is_public, rng)
    }

    /// Initializes a new transfer request.
    pub fn new_transfer<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        records: Vec<Record<N>>,
        ledger_proofs: Vec<LedgerProof<N>>,
        recipient: Address<N>,
        amount: AleoAmount,
        is_public: bool,
        rng: &mut R,
    ) -> Result<Self> {
        let operation = Operation::Transfer(caller.to_address(), recipient, amount);

        let total_balance = records.iter().map(|record| record.value()).sum::<AleoAmount>();
        let fee = total_balance.sub(amount);

        Self::new(caller, records, ledger_proofs, operation, fee, is_public, rng)
    }

    /// Returns a new instance of a noop request.
    pub fn new_noop<R: Rng + CryptoRng>(ledger_proofs: Vec<LedgerProof<N>>, rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_address = Address::from_private_key(&noop_private_key);

        // Construct the noop.
        let records = vec![Record::new_noop(noop_address, rng)?];

        Self::new(&noop_private_key, records, ledger_proofs, Operation::Noop, AleoAmount::ZERO, false, rng)
    }

    /// Signs and returns a new instance of a request.
    pub fn new<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        records: Vec<Record<N>>,
        ledger_proofs: Vec<LedgerProof<N>>,
        operation: Operation<N>,
        fee: AleoAmount,
        is_public: bool,
        rng: &mut R,
    ) -> Result<Self> {
        let caller_address = Address::from_private_key(caller);

        if records.is_empty() && !operation.is_coinbase() {
            return Err(anyhow!("There must be at least one record consumed."));
        }

        let mut signatures = Vec::with_capacity(N::NUM_INPUTS as usize);
        for record in records.iter() {
            // Ensure the caller and record owner match.
            if caller_address != record.owner() {
                return Err(anyhow!("Address from caller private key does not match record owner"));
            }
            let message =
                to_bytes_le![record.commitment(), record.program_id().unwrap_or_default() /*operation_id, fee*/]?;
            let signature = caller.sign(&message.to_bits_le(), rng)?;

            signatures.push(signature);
        }

        Self::from(records, ledger_proofs, operation, fee, signatures, is_public)
    }

    /// Returns a new instance of a request.
    pub fn from(
        records: Vec<Record<N>>,
        ledger_proofs: Vec<LedgerProof<N>>,
        operation: Operation<N>,
        fee: AleoAmount,
        signatures: Vec<N::AccountSignature>,
        is_public: bool,
    ) -> Result<Self> {
        let request = Self { records, operation, ledger_proofs, fee, signatures, is_public };

        match request.is_valid() {
            true => Ok(request),
            false => Err(anyhow!("Request is not well-formed")),
        }
    }

    /// Returns `true` if the request signature is valid.
    pub fn is_valid(&self) -> bool {
        // Ensure the number of records is correct.
        if self.records.len() > (N::NUM_INPUTS as usize) {
            eprintln!("Incorrect number of request records. Maximum {}, found {}", N::NUM_INPUTS, self.records.len());
            return false;
        }

        // Ensure the number of ledger proofs is correct.
        if self.ledger_proofs.len() != self.records.len() {
            eprintln!(
                "Incorrect number of request ledger proofs. Expected {}, found {}",
                self.records.len(),
                self.ledger_proofs.len()
            );
            return false;
        }

        // Ensure the records contain the same owner, and retrieve the owner as the caller.
        let owners: HashSet<Address<N>> = self.records.iter().map(|record| record.owner()).collect();
        if owners.len() > 1 {
            eprintln!("Request records do not contain the same owner");
            return false;
        }

        // Ensure the records contains a total value that is at least the fee amount.
        if !self.operation.is_coinbase() {
            let balance: AleoAmount = self.records.iter().map(|record| record.value()).sum();
            if balance < self.fee {
                eprintln!("Request records do not contain sufficient value for fee");
                return false;
            }

            // Ensure that the total value is equivalent to the recipient amount and fee
            if let Operation::Transfer(_, _, amount) = &self.operation {
                if balance != self.fee.add(*amount) {
                    eprintln!("Request records do not contain the correct value");
                    return false;
                }
            }
        } else if !self.records.is_empty() {
            eprintln!("Coinbase request must have no input records.");
            return false;
        }

        // Ensure the records contain at most 1 program ID, and retrieve the program ID.
        let program_id = {
            let program_id = OnceCell::new();
            for record in &self.records {
                if record.program_id().is_some() && program_id.set(record.program_id()).is_err() {
                    eprintln!("Request records contains more than 1 distinct program ID");
                    return false;
                }
            }
            *program_id.get_or_init(|| None)
        };

        // If there is no program id, ensure there is no function ID.
        if program_id == None && self.function_id() != None {
            eprintln!("Request contains mismatching program ID and function ID");
            return false;
        }

        // Ensure the function ID is in the specified program.
        {}

        // Ensure the given record commitments are in the specified ledger proofs.
        {}

        // Verify the request signatures.
        for (i, (record, signature)) in self.records.iter().zip_eq(&self.signatures).enumerate() {
            // Prepare for signature verification.
            let message = match to_bytes_le![
                record.commitment(),
                record.program_id().unwrap_or_default() /*operation_id, self.fee*/
            ] {
                Ok(signature_message) => signature_message.to_bits_le(),
                Err(error) => {
                    eprintln!("Failed to construct record {} request signature message: {}", i, error);
                    return false;
                }
            };

            // Ensure the signature is valid.
            if let Err(error) = N::account_signature_scheme().verify(&record.owner(), &message, signature) {
                eprintln!("Failed to verify request signature {}: {}", i, error);
                return false;
            }
        }

        true
    }

    /// Returns a reference to the records.
    pub fn records(&self) -> &Vec<Record<N>> {
        &self.records
    }

    /// Returns the ledger roots used to prove inclusion of ledger-consumed records.
    pub fn ledger_roots(&self) -> Vec<N::LedgerRoot> {
        self.ledger_proofs.iter().map(LedgerProof::ledger_root).collect()
    }

    /// Returns a reference to the ledger proofs.
    pub fn ledger_proofs(&self) -> &Vec<LedgerProof<N>> {
        &self.ledger_proofs
    }

    /// Returns the function ID.
    pub fn function_id(&self) -> Option<N::FunctionID> {
        self.operation.function_id()
    }

    /// Returns a reference to the operation.
    pub fn operation(&self) -> &Operation<N> {
        &self.operation
    }

    /// Returns the visibility of the operation.
    pub fn is_public(&self) -> bool {
        self.is_public
    }

    /// Returns the fee.
    pub fn fee(&self) -> AleoAmount {
        self.fee
    }

    /// Returns a reference to the signatures.
    pub fn signatures(&self) -> &Vec<N::AccountSignature> {
        &self.signatures
    }

    /// Returns the caller of the request.
    pub fn caller(&self) -> Result<Address<N>> {
        let owners: HashSet<Address<N>> = self.records.iter().map(Record::owner).collect();
        match owners.len() == 1 {
            true => owners.into_iter().next().ok_or_else(|| anyhow!("Failed to retrieve the request caller")),
            false => Err(anyhow!("Request records do not contain the same owner")),
        }
    }

    /// Returns the balance of the caller.
    pub fn to_balance(&self) -> AleoAmount {
        self.records.iter().map(|record| record.value()).sum()
    }

    /// Returns the program ID.
    pub fn to_program_id(&self) -> Result<Option<N::ProgramID>> {
        let program_id = OnceCell::new();
        for record in &self.records {
            if record.program_id().is_some() && program_id.set(record.program_id()).is_err() {
                return Err(anyhow!("Request records contains more than 1 distinct program ID"));
            }
        }
        Ok(*program_id.get_or_init(|| None))
    }

    /// Returns the serial numbers.
    pub fn to_serial_numbers(&self) -> Result<Vec<N::SerialNumber>> {
        self.records
            .iter()
            .zip_eq(&self.signatures)
            .map(|(record, signature)| {
                let compute_key = ComputeKey::from_signature(signature)?;
                Ok(record.to_serial_number(&compute_key)?)
            })
            .collect::<Result<Vec<_>>>()
    }

    /// Returns the input commitments.
    pub fn to_input_commitments(&self) -> Vec<N::Commitment> {
        self.records.iter().map(|record| record.commitment()).collect()
    }
}

impl<N: Network> FromBytes for Request<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let num_records: u32 = FromBytes::read_le(&mut reader)?;
        let mut records = Vec::with_capacity(num_records as usize);
        for _ in 0..num_records {
            records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut ledger_proofs = Vec::with_capacity(num_records as usize);
        for _ in 0..num_records {
            ledger_proofs.push(FromBytes::read_le(&mut reader)?);
        }

        let operation = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;

        let mut signatures = Vec::with_capacity(num_records as usize);
        for _ in 0..num_records {
            signatures.push(FromBytes::read_le(&mut reader)?);
        }

        let is_public = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(records, ledger_proofs, operation, fee, signatures, is_public)
            .expect("Failed to deserialize a request"))
    }
}

impl<N: Network> ToBytes for Request<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.records.len() as u32).write_le(&mut writer)?;
        self.records.write_le(&mut writer)?;
        self.ledger_proofs.write_le(&mut writer)?;
        self.operation.write_le(&mut writer)?;
        self.fee.write_le(&mut writer)?;
        self.signatures.write_le(&mut writer)?;
        self.is_public.write_le(&mut writer)
    }
}

impl<N: Network> fmt::Display for Request<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
