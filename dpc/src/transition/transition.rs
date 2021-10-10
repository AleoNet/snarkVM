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

use crate::{prelude::*, Network};
use snarkvm_algorithms::traits::{CRH, SNARK};
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use std::{
    fmt,
    io::{Read, Result as IoResult, Write},
};

#[derive(Derivative)]
#[derivative(
    Clone(bound = "N: Network"),
    PartialEq(bound = "N: Network"),
    Eq(bound = "N: Network")
)]
pub struct Transition<N: Network> {
    /// The ID of this transition.
    transition_id: N::TransitionID,
    /// The block hash used to prove inclusion of ledger-consumed records.
    block_hash: N::BlockHash,
    /// The local commitments root used to prove inclusion of locally-consumed records.
    local_commitments_root: N::LocalCommitmentsRoot,
    /// The serial numbers of the input records.
    serial_numbers: Vec<N::SerialNumber>,
    /// The commitments of the output records.
    commitments: Vec<N::Commitment>,
    /// The ciphertexts of the output records.
    ciphertexts: Vec<RecordCiphertext<N>>,
    /// A value balance is the difference between the input and output record values.
    value_balance: AleoAmount,
    #[derivative(PartialEq = "ignore")]
    /// The zero-knowledge proof attesting to the validity of the transition.
    proof: <N::OuterSNARK as SNARK>::Proof,
}

impl<N: Network> Transition<N> {
    /// Initializes a new instance of a transition.
    #[inline]
    pub(crate) fn from<R: Rng + CryptoRng>(request: &Request<N>, response: &Response<N>, rng: &mut R) -> Result<Self> {
        // Fetch the block hash, local commitments root, and serial numbers.
        let block_hash = request.block_hash();
        let local_commitments_root = request.local_commitments_root();
        let serial_numbers = request.to_serial_numbers()?;
        let program_id = request.to_program_id()?;

        // Fetch the commitments and ciphertexts.
        let commitments = response.to_commitments();
        let ciphertexts = response.ciphertexts().clone();

        // Compute the value balance.
        let mut value_balance = AleoAmount::ZERO;
        for record in request.records().iter().take(N::NUM_INPUT_RECORDS) {
            value_balance = value_balance.add(AleoAmount::from_bytes(record.value() as i64));
        }
        for record in response.records().iter().take(N::NUM_OUTPUT_RECORDS) {
            value_balance = value_balance.sub(AleoAmount::from_bytes(record.value() as i64));
        }

        // Compute the transition ID.
        let transition_id = Self::compute_transition_id(
            block_hash,
            local_commitments_root,
            &serial_numbers,
            &commitments,
            &ciphertexts,
            value_balance,
        )?;

        // Compute the noop execution, for now.
        // let execution = response.execution();
        let execution = Execution {
            program_id: *N::noop_program_id(),
            program_path: N::noop_program_path().clone(),
            verifying_key: N::noop_circuit_verifying_key().clone(),
            proof: Noop::<N>::new().execute(ProgramPublicVariables::new(transition_id))?,
        };

        // Compute the inner circuit proof, and verify that the inner proof passes.
        let inner_public = InnerPublicVariables::new(transition_id, Some(program_id));
        let inner_private = InnerPrivateVariables::new(&request, &response)?;
        let inner_circuit = InnerCircuit::<N>::new(inner_public.clone(), inner_private);
        let inner_proof = N::InnerSNARK::prove(N::inner_proving_key(), &inner_circuit, rng)?;

        assert!(N::InnerSNARK::verify(
            N::inner_verifying_key(),
            &inner_public,
            &inner_proof
        )?);

        // Construct the outer circuit public and private variables.
        let outer_public = OuterPublicVariables::new(transition_id, *N::inner_circuit_id());
        let outer_private = OuterPrivateVariables::new(N::inner_verifying_key().clone(), inner_proof, execution);
        let outer_circuit = OuterCircuit::<N>::new(outer_public.clone(), outer_private);
        let outer_proof = N::OuterSNARK::prove(N::outer_proving_key(), &outer_circuit, rng)?;

        assert!(N::OuterSNARK::verify(
            N::outer_verifying_key(),
            &outer_public,
            &outer_proof
        )?);

        // Construct the transition.
        Ok(Self {
            transition_id,
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
            proof: outer_proof,
        })
    }

    /// Returns `true` if the transition proof is valid, and the local commitments root matches.
    #[inline]
    pub fn verify(&self, inner_circuit_id: N::InnerCircuitID, local_commitments_root: N::LocalCommitmentsRoot) -> bool {
        // Returns `false` if the local commitments root does not match the given one.
        if self.local_commitments_root != local_commitments_root {
            eprintln!(
                "Transition contains incorrect local commitments root: {} != {}",
                self.local_commitments_root, local_commitments_root
            );
            return false;
        }

        // Returns `false` if the transition proof is invalid.
        match N::OuterSNARK::verify(
            N::outer_verifying_key(),
            &OuterPublicVariables::new(self.transition_id, inner_circuit_id),
            &self.proof,
        ) {
            Ok(is_valid) => match is_valid {
                true => true,
                false => {
                    eprintln!("Transition proof failed to verify");
                    return false;
                }
            },
            Err(error) => {
                eprintln!("Failed to validate transition proof: {:?}", error);
                return false;
            }
        }
    }

    /// Returns the transition ID.
    #[inline]
    pub(crate) fn transition_id(&self) -> N::TransitionID {
        self.transition_id
    }

    /// Returns the block hash used to prove inclusion of ledger-consumed records.
    #[inline]
    pub(crate) fn block_hash(&self) -> N::BlockHash {
        self.block_hash
    }

    /// Returns the local commitments root used to prove inclusion of locally-consumed records.
    #[inline]
    pub(crate) fn local_commitments_root(&self) -> N::LocalCommitmentsRoot {
        self.local_commitments_root
    }

    /// Returns a reference to the serial numbers.
    #[inline]
    pub(crate) fn serial_numbers(&self) -> &Vec<N::SerialNumber> {
        &self.serial_numbers
    }

    /// Returns a reference to the commitments.
    #[inline]
    pub(crate) fn commitments(&self) -> &Vec<N::Commitment> {
        &self.commitments
    }

    /// Returns a reference to the ciphertexts.
    #[inline]
    pub(crate) fn ciphertexts(&self) -> &Vec<RecordCiphertext<N>> {
        &self.ciphertexts
    }

    /// Returns a reference to the value balance.
    #[inline]
    pub(crate) fn value_balance(&self) -> &AleoAmount {
        &self.value_balance
    }

    /// Returns a reference to the transition proof.
    #[inline]
    pub(crate) fn proof(&self) -> &<N::OuterSNARK as SNARK>::Proof {
        &self.proof
    }

    /// Returns the ciphertext IDs.
    #[inline]
    pub(crate) fn to_ciphertext_ids(&self) -> impl Iterator<Item = Result<N::CiphertextID>> + fmt::Debug + '_ {
        self.ciphertexts.iter().map(RecordCiphertext::to_ciphertext_id)
    }

    /// Transition ID := Hash(block hash || local commitments root || serial numbers || commitments || ciphertext_ids || value balance)
    fn compute_transition_id(
        block_hash: N::BlockHash,
        local_commitments_root: N::LocalCommitmentsRoot,
        serial_numbers: &Vec<N::SerialNumber>,
        commitments: &Vec<N::Commitment>,
        ciphertexts: &Vec<RecordCiphertext<N>>,
        value_balance: AleoAmount,
    ) -> Result<N::TransitionID> {
        Ok(N::transition_id_crh().hash(&to_bytes_le![
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts
                .iter()
                .map(RecordCiphertext::to_ciphertext_id)
                .collect::<Result<Vec<_>>>()?,
            value_balance
        ]?)?)
    }
}

impl<N: Network> ToBytes for Transition<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.block_hash.write_le(&mut writer)?;
        self.local_commitments_root.write_le(&mut writer)?;
        self.serial_numbers.write_le(&mut writer)?;
        self.commitments.write_le(&mut writer)?;
        self.ciphertexts.write_le(&mut writer)?;
        self.value_balance.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for Transition<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let block_hash = FromBytes::read_le(&mut reader)?;
        let local_commitments_root = FromBytes::read_le(&mut reader)?;

        let mut serial_numbers = Vec::<N::SerialNumber>::with_capacity(N::NUM_INPUT_RECORDS);
        for _ in 0..N::NUM_INPUT_RECORDS {
            serial_numbers.push(FromBytes::read_le(&mut reader)?);
        }

        let mut commitments = Vec::<N::Commitment>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            commitments.push(FromBytes::read_le(&mut reader)?);
        }

        let mut ciphertexts = Vec::<RecordCiphertext<N>>::with_capacity(N::NUM_OUTPUT_RECORDS);
        for _ in 0..N::NUM_OUTPUT_RECORDS {
            ciphertexts.push(FromBytes::read_le(&mut reader)?);
        }

        let value_balance: AleoAmount = FromBytes::read_le(&mut reader)?;
        let proof: <N::OuterSNARK as SNARK>::Proof = FromBytes::read_le(&mut reader)?;

        let transition_id = Self::compute_transition_id(
            block_hash,
            local_commitments_root,
            &serial_numbers,
            &commitments,
            &ciphertexts,
            value_balance,
        )
        .expect("Failed to compute the transition ID during deserialization");

        Ok(Self {
            transition_id,
            block_hash,
            local_commitments_root,
            serial_numbers,
            commitments,
            ciphertexts,
            value_balance,
            proof,
        })
    }
}

// TODO (raychu): add debug support for record ciphertexts
impl<N: Network> fmt::Debug for Transition<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Transition {{ transition_id: {:?}, block_hash: {:?}, local_commitments_root: {:?}, serial_numbers: {:?}, commitments: {:?}, ciphertext_ids: {:?}, value_balance: {:?}, proof: {:?} }}",
            self.transition_id(),
            self.block_hash(),
            self.local_commitments_root(),
            self.serial_numbers(),
            self.commitments(),
            self.to_ciphertext_ids(),
            self.value_balance(),
            self.proof()
        )
    }
}
