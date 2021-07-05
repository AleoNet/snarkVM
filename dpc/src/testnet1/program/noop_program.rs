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
    testnet1::{LocalData, NoopCircuit, PrivateProgramInput, ProgramLocalData, Testnet1Components},
    DPCComponents,
    ProgramError,
    ProgramScheme,
    RecordScheme,
};
use snarkvm_algorithms::{CommitmentScheme, CRH, SNARK};
use snarkvm_utilities::{to_bytes, ToBytes};

use rand::Rng;

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Testnet1Components"), Debug(bound = "C: Testnet1Components"))]
pub struct NoopProgram<C: Testnet1Components> {
    #[derivative(Default(value = "vec![0u8; 48]"))]
    id: Vec<u8>,
    #[derivative(Debug = "ignore")]
    proving_key: <<C as Testnet1Components>::NoopProgramSNARK as SNARK>::ProvingKey,
    #[derivative(Debug = "ignore")]
    verifying_key: <<C as Testnet1Components>::NoopProgramSNARK as SNARK>::VerifyingKey,
}

impl<C: Testnet1Components> ProgramScheme for NoopProgram<C> {
    type ID = Vec<u8>;
    type LocalData = LocalData<C>;
    type PrivateWitness = PrivateProgramInput;
    type ProgramIDCRH = C::ProgramVerificationKeyCRH;
    type ProofSystem = <C as Testnet1Components>::NoopProgramSNARK;
    type ProvingKey = <Self::ProofSystem as SNARK>::ProvingKey;
    type PublicInput = ();
    type VerifyingKey = <Self::ProofSystem as SNARK>::VerifyingKey;

    /// Initializes a new instance of a program.
    fn new(
        program_id_crh_parameters: &Self::ProgramIDCRH,
        proving_key: Self::ProvingKey,
        verifying_key: Self::VerifyingKey,
    ) -> Result<Self, ProgramError> {
        // Compute the program ID.
        let program_id = to_bytes![<C as DPCComponents>::ProgramVerificationKeyCRH::hash(
            program_id_crh_parameters,
            &to_bytes![verifying_key]?
        )?]?;

        Ok(Self {
            id: program_id,
            proving_key,
            verifying_key,
        })
    }

    /// Returns the program ID.
    fn id(&self) -> Self::ID {
        self.id.clone()
    }

    fn execute<R: Rng>(
        &self,
        local_data: &Self::LocalData,
        position: u8,
        rng: &mut R,
    ) -> Result<Self::PrivateWitness, ProgramError> {
        let num_records = local_data.old_records.len() + local_data.new_records.len();
        assert!((position as usize) < num_records);

        let record = if (position as usize) < local_data.old_records.len() {
            &local_data.old_records[position as usize]
        } else {
            &local_data.new_records[position as usize - local_data.old_records.len()]
        };

        if (position as usize) < C::NUM_INPUT_RECORDS {
            assert_eq!(self.id, record.death_program_id());
        } else {
            assert_eq!(self.id, record.birth_program_id());
        }

        let local_data_root = local_data.local_data_merkle_tree.root();

        let circuit = NoopCircuit::<C>::new(&local_data.system_parameters, &local_data_root, position);

        let proof = <Self::ProofSystem as SNARK>::prove(&self.proving_key, &circuit, rng)?;

        {
            let program_snark_pvk: <Self::ProofSystem as SNARK>::PreparedVerifyingKey =
                self.verifying_key.clone().into();

            let program_pub_input: ProgramLocalData<C> = ProgramLocalData {
                local_data_commitment_parameters: local_data
                    .system_parameters
                    .local_data_commitment
                    .parameters()
                    .clone(),
                local_data_root,
                position,
            };
            assert!(<Self::ProofSystem as SNARK>::verify(
                &program_snark_pvk,
                &program_pub_input,
                &proof
            )?);
        }

        Ok(Self::PrivateWitness {
            verifying_key: to_bytes![self.verifying_key]?,
            proof: to_bytes![proof]?,
        })
    }

    fn evaluate(&self, _p: &Self::PublicInput, _w: &Self::PrivateWitness) -> bool {
        unimplemented!()
    }

    fn into_compact_repr(&self) -> Vec<u8> {
        self.id.clone()
    }
}
