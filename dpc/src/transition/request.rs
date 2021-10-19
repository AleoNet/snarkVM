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

use crate::{Address, AleoAmount, ComputeKey, FunctionType, LedgerProof, Network, Operation, PrivateKey, Record};
use snarkvm_algorithms::SignatureScheme;
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{anyhow, Result};
use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use std::{
    collections::HashSet,
    fmt,
    io::{Read, Result as IoResult, Write},
};

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
    /// The signature for the request.
    signature: N::AccountSignature,
}

impl<N: Network> Request<N> {
    /// Initializes a new coinbase generation.
    pub fn new_coinbase<R: Rng + CryptoRng>(recipient: Address<N>, amount: AleoAmount, rng: &mut R) -> Result<Self> {
        let burner = PrivateKey::new(rng);
        let operation = Operation::Coinbase(recipient, amount);
        let fee = AleoAmount::ZERO.sub(amount);
        Self::new(
            &burner,
            vec![],
            vec![LedgerProof::default(); N::NUM_INPUT_RECORDS],
            operation,
            fee,
            rng,
        )
    }

    /// Initializes a new transfer request.
    pub fn new_transfer<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        records: Vec<Record<N>>,
        ledger_proofs: Vec<LedgerProof<N>>,
        recipient: Address<N>,
        amount: AleoAmount,
        fee: AleoAmount,
        rng: &mut R,
    ) -> Result<Self> {
        let operation = Operation::Transfer(caller.to_address(), recipient, amount);
        Self::new(caller, records, ledger_proofs, operation, fee, rng)
    }

    /// Returns a new instance of a noop request.
    pub fn new_noop<R: Rng + CryptoRng>(ledger_proofs: Vec<LedgerProof<N>>, rng: &mut R) -> Result<Self> {
        // Sample a burner noop private key.
        let noop_private_key = PrivateKey::new(rng);
        let noop_address = Address::from_private_key(&noop_private_key);

        // Construct the noop records.
        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            records.push(Record::new_noop_input(noop_address, rng)?);
        }

        Self::new(
            &noop_private_key,
            records,
            ledger_proofs,
            Operation::Noop,
            AleoAmount::ZERO,
            rng,
        )
    }

    /// Signs and returns a new instance of a request.
    pub fn new<R: Rng + CryptoRng>(
        caller: &PrivateKey<N>,
        records: Vec<Record<N>>,
        ledger_proofs: Vec<LedgerProof<N>>,
        operation: Operation<N>,
        fee: AleoAmount,
        rng: &mut R,
    ) -> Result<Self> {
        let caller_address = Address::from_private_key(caller);

        // Pad the records with noops if there is less than required.
        let mut records = records;
        while records.len() < N::NUM_INPUT_RECORDS {
            records.push(Record::new_noop_input(caller_address, rng)?);
        }

        let mut commitments = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for record in records.iter().take(N::NUM_INPUT_RECORDS) {
            // Ensure the caller and record owner match.
            if caller_address != record.owner() {
                return Err(anyhow!("Address from caller private key does not match record owner"));
            }
            commitments.push(record.commitment());
        }

        let message = to_bytes_le![commitments /*operation_id, fee*/]?;
        let signature = caller.sign(&message, rng)?;

        Self::from(records, ledger_proofs, operation, fee, signature)
    }

    /// Returns a new instance of a request.
    pub fn from(
        records: Vec<Record<N>>,
        ledger_proofs: Vec<LedgerProof<N>>,
        operation: Operation<N>,
        fee: AleoAmount,
        signature: N::AccountSignature,
    ) -> Result<Self> {
        let request = Self {
            records,
            operation,
            ledger_proofs,
            fee,
            signature,
        };

        match request.is_valid() {
            true => Ok(request),
            false => Err(anyhow!("Request is not well-formed")),
        }
    }

    /// Returns `true` if the request signature is valid.
    pub fn is_valid(&self) -> bool {
        // Ensure the number of records is correct.
        if self.records.len() != N::NUM_INPUT_RECORDS {
            eprintln!(
                "Incorrect number of request records. Expected {}, found {}",
                N::NUM_INPUT_RECORDS,
                self.records.len()
            );
            return false;
        }

        // Ensure the number of ledger proofs is correct.
        if self.ledger_proofs.len() != N::NUM_INPUT_RECORDS {
            eprintln!(
                "Incorrect number of request ledger proofs. Expected {}, found {}",
                N::NUM_INPUT_RECORDS,
                self.ledger_proofs.len()
            );
            return false;
        }

        // Ensure the records contain the same owner, and retrieve the owner as the caller.
        let caller = {
            let owners: HashSet<Address<N>> = self.records.iter().map(|record| record.owner()).collect();
            if owners.len() == 1 {
                *owners.iter().next().expect("Failed to fetch request caller")
            } else {
                eprintln!("Request records do not contain the same owner");
                return false;
            }
        };

        // Ensure the records contains a total value that is at least the fee amount.
        if !self.operation.is_coinbase() {
            let balance: u64 = self.records.iter().map(|record| record.value()).sum();
            if AleoAmount(balance as i64) < self.fee {
                eprintln!("Request records do not contain sufficient value for fee");
                return false;
            }
        }

        // Ensure the records contain at most 1 program ID, and retrieve the program ID.
        let program_id = {
            let program_id = OnceCell::new();
            for record in &self.records {
                if record.program_id() != *N::noop_program_id() {
                    if program_id.set(record.program_id()).is_err() {
                        eprintln!("Request records contains more than 1 distinct program ID");
                        return false;
                    }
                }
            }
            *program_id.get_or_init(|| *N::noop_program_id())
        };

        // If the program ID is the noop program ID, ensure the function ID is the noop function ID.
        if program_id == *N::noop_program_id() && self.function_id() != *N::noop_function_id() {
            eprintln!("Request contains mismatching program ID and function ID");
            return false;
        }

        // Ensure the function ID is in the specified program.
        {}

        // Ensure the given record commitments are in the specified ledger proofs.
        {}

        // Prepare for signature verification.
        let commitments: Vec<_> = self.records.iter().map(|record| record.commitment()).collect();
        let message = match to_bytes_le![commitments /*operation_id, self.fee*/] {
            Ok(signature_message) => signature_message,
            Err(error) => {
                eprintln!("Failed to construct request signature message: {}", error);
                return false;
            }
        };

        // Ensure the signature is valid.
        match N::account_signature_scheme().verify(&caller, &message, &self.signature) {
            Ok(is_valid) => is_valid,
            Err(error) => {
                eprintln!("Failed to verify request signature: {}", error);
                false
            }
        }
    }

    /// Returns `true` if the request calls the noop program and function.
    pub fn is_noop(&self) -> bool {
        self.to_program_id().unwrap() == *N::noop_program_id() && self.function_id() == *N::noop_function_id()
    }

    /// Returns a reference to the records.
    pub fn records(&self) -> &Vec<Record<N>> {
        &self.records
    }

    /// Returns the ledger roots used to prove inclusion of ledger-consumed records.
    pub fn ledger_roots(&self) -> Vec<N::LedgerRoot> {
        self.ledger_proofs.iter().map(LedgerProof::ledger_root).collect()
    }

    /// Returns a reference to the ledger proof.
    pub fn ledger_proofs(&self) -> &Vec<LedgerProof<N>> {
        &self.ledger_proofs
    }

    /// Returns the function ID.
    pub fn function_id(&self) -> N::FunctionID {
        self.operation.function_id()
    }

    /// Returns the function type.
    pub fn function_type(&self) -> FunctionType {
        self.operation.function_type()
    }

    /// Returns a reference to the operation.
    pub fn operation(&self) -> &Operation<N> {
        &self.operation
    }

    /// Returns the fee.
    pub fn fee(&self) -> AleoAmount {
        self.fee
    }

    /// Returns a reference to the signature.
    pub fn signature(&self) -> &N::AccountSignature {
        &self.signature
    }

    /// Returns the caller of the request.
    pub fn caller(&self) -> Result<Address<N>> {
        let owners: HashSet<Address<N>> = self.records.iter().map(Record::owner).collect();
        match owners.len() == 1 {
            true => owners
                .into_iter()
                .next()
                .ok_or(anyhow!("Failed to retrieve the request caller")),
            false => Err(anyhow!("Request records do not contain the same owner")),
        }
    }

    /// Returns the balance of the caller.
    pub fn to_balance(&self) -> AleoAmount {
        AleoAmount(self.records.iter().map(|record| record.value()).sum::<u64>() as i64)
    }

    /// Returns the program ID.
    pub fn to_program_id(&self) -> Result<N::ProgramID> {
        let program_id = OnceCell::new();
        for record in &self.records {
            if record.program_id() != *N::noop_program_id() {
                if program_id.set(record.program_id()).is_err() {
                    return Err(anyhow!("Request records contains more than 1 distinct program ID"));
                }
            }
        }
        Ok(*program_id.get_or_init(|| *N::noop_program_id()))
    }

    /// Returns the serial numbers.
    pub fn to_serial_numbers(&self) -> Result<Vec<N::SerialNumber>> {
        self.records
            .iter()
            .map(|record| Ok(record.to_serial_number(&ComputeKey::from_signature(&self.signature)?)?))
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
        let mut records = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            records.push(FromBytes::read_le(&mut reader)?);
        }

        let mut ledger_proofs = Vec::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            ledger_proofs.push(FromBytes::read_le(&mut reader)?);
        }

        let operation = FromBytes::read_le(&mut reader)?;
        let fee = FromBytes::read_le(&mut reader)?;
        let signature = FromBytes::read_le(&mut reader)?;

        Ok(Self::from(records, ledger_proofs, operation, fee, signature).expect("Failed to deserialize a request"))
    }
}

impl<N: Network> ToBytes for Request<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.records.write_le(&mut writer)?;
        self.ledger_proofs.write_le(&mut writer)?;
        self.operation.write_le(&mut writer)?;
        self.fee.write_le(&mut writer)?;
        self.signature.write_le(&mut writer)
    }
}

impl<N: Network> fmt::Display for Request<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
