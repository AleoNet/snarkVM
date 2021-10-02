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

use crate::{Execution, Network, OuterPrivateVariables, OuterPublicVariables};
use snarkvm_algorithms::{merkle_tree::MerkleTreeDigest, traits::SNARK};
use snarkvm_fields::ToConstraintField;
use snarkvm_gadgets::{
    algorithms::merkle_tree::MerklePathGadget,
    bits::ToBytesGadget,
    traits::{
        algorithms::{CRHGadget, SNARKVerifierGadget},
        alloc::AllocGadget,
        eq::EqGadget,
    },
    MergeGadget,
    ToBitsLEGadget,
    ToMinimalBitsGadget,
    UInt8,
};
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};
use snarkvm_utilities::ToBytes;

use itertools::Itertools;

#[derive(Derivative)]
#[derivative(Clone(bound = "N: Network"))]
pub struct OuterCircuit<N: Network> {
    public: OuterPublicVariables<N>,
    private: OuterPrivateVariables<N>,
}

impl<N: Network> OuterCircuit<N> {
    pub fn blank(
        inner_snark_vk: <N::InnerSNARK as SNARK>::VerifyingKey,
        inner_snark_proof: <N::InnerSNARK as SNARK>::Proof,
        execution: Execution<N>,
    ) -> Self {
        Self {
            public: OuterPublicVariables::blank(),
            private: OuterPrivateVariables::blank(inner_snark_vk, inner_snark_proof, execution),
        }
    }

    pub fn new(public: OuterPublicVariables<N>, private: OuterPrivateVariables<N>) -> Self {
        Self { public, private }
    }
}

impl<N: Network> ConstraintSynthesizer<N::OuterScalarField> for OuterCircuit<N>
where
    MerkleTreeDigest<N::CommitmentsTreeParameters>: ToConstraintField<N::InnerScalarField>,
{
    fn generate_constraints<CS: ConstraintSystem<N::OuterScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        execute_outer_circuit::<N, CS>(cs, &self.public, &self.private)
    }
}

pub fn execute_outer_circuit<N: Network, CS: ConstraintSystem<N::OuterScalarField>>(
    cs: &mut CS,
    public: &OuterPublicVariables<N>,
    private: &OuterPrivateVariables<N>,
) -> Result<(), SynthesisError> {
    // Access the outer public variables.
    let OuterPublicVariables {
        inner_public_variables: inner_public,
        inner_circuit_id,
    } = public;

    // In the outer circuit, thus variable must be allocated as private input,
    // as it is not included in the transaction.
    debug_assert!(inner_public.program_id.is_none());

    // ************************************************************************
    // Declare public parameters.
    // ************************************************************************

    let program_circuit_id_crh = N::ProgramCircuitIDCRHGadget::alloc_constant(
        &mut cs.ns(|| "Declare program_circuit_id_crh_parameters"),
        || Ok(N::program_circuit_id_crh().clone()),
    )?;

    let program_circuits_tree_crh = N::ProgramCircuitsTreeCRHGadget::alloc_constant(
        &mut cs.ns(|| "Declare program_circuits_tree_crh_parameters"),
        || Ok(N::program_circuits_tree_crh().clone()),
    )?;

    let inner_circuit_id_crh =
        N::InnerCircuitIDCRHGadget::alloc_constant(&mut cs.ns(|| "Declare inner_circuit_id_crh_parameters"), || {
            Ok(N::inner_circuit_id_crh().clone())
        })?;

    // ************************************************************************
    // Construct the inner circuit input.
    // ************************************************************************

    // Declare inner circuit public variables as inner circuit field elements

    let ledger_digest_fe =
        alloc_inner_snark_input_field_element::<N, _, _>(cs, &inner_public.ledger_digest, "ledger digest")?;

    let serial_number_fe = {
        let mut serial_number_fe_vec = Vec::with_capacity(inner_public.kernel.serial_numbers().len());
        for (index, sn) in inner_public.kernel.serial_numbers().iter().enumerate() {
            let this_serial_number_fe =
                alloc_inner_snark_input_field_element::<N, _, _>(cs, sn, &format!("serial number {}", index))?;

            serial_number_fe_vec.push(this_serial_number_fe);
        }

        <N::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::merge_many(
            cs.ns(|| "serial number"),
            &serial_number_fe_vec,
        )?
    };

    let commitment_and_encrypted_record_hash_fe = {
        let mut commitment_and_encrypted_record_hash_fe_vec =
            Vec::with_capacity(inner_public.kernel.commitments().len() * N::NUM_OUTPUT_RECORDS);
        for (index, (cm, encrypted_record_hash)) in inner_public
            .kernel
            .commitments()
            .iter()
            .zip_eq(inner_public.encrypted_record_ids.iter())
            .enumerate()
        {
            let commitment_fe =
                alloc_inner_snark_input_field_element::<N, _, _>(cs, cm, &format!("commitment {}", index))?;
            let encrypted_record_hash_fe = alloc_inner_snark_input_field_element::<N, _, _>(
                cs,
                encrypted_record_hash,
                &format!("encrypted_record_hash {}", index),
            )?;

            commitment_and_encrypted_record_hash_fe_vec.push(commitment_fe);
            commitment_and_encrypted_record_hash_fe_vec.push(encrypted_record_hash_fe);
        }

        <N::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::merge_many(
            cs.ns(|| "commitment_and_encrypted_record_hash"),
            &commitment_and_encrypted_record_hash_fe_vec,
        )?
    };

    let value_balance_fe = alloc_inner_snark_input_field_element::<N, _, _>(
        cs,
        &inner_public.kernel.value_balance().0.to_le_bytes(),
        "value balance",
    )?;

    let memo_fe = alloc_inner_snark_input_field_element::<N, _, _>(cs, inner_public.kernel.memo(), "memo")?;

    let network_id_fe = alloc_inner_snark_input_field_element::<N, _, _>(
        cs,
        &inner_public.kernel.network_id().to_le_bytes(),
        "network id",
    )?;

    let program_id_fe = alloc_inner_snark_field_element::<N, _, _>(
        cs,
        &private.program_execution.program_id.to_bytes_le()?[..],
        "program ID",
    )?;

    let transaction_id_fe_inner_snark = alloc_inner_snark_input_field_element::<N, _, _>(
        cs,
        &inner_public.kernel.to_transaction_id()?,
        "transaction ID inner snark",
    )?;
    let transaction_id_fe_program_snark = alloc_program_snark_field_element::<N, _, _>(
        cs,
        &inner_public.kernel.to_transaction_id()?,
        "transaction ID program snark",
    )?;
    {
        // Construct inner snark input as bits
        let transaction_id_input_inner_snark_bits =
            transaction_id_fe_inner_snark.to_bits_le(cs.ns(|| "transaction ID inner snark to bits"))?;
        let transaction_id_input_program_snark_bits =
            transaction_id_fe_program_snark.to_bits_le(cs.ns(|| "transaction ID program snark to bits"))?;
        transaction_id_input_inner_snark_bits.enforce_equal(
            cs.ns(|| "transaction ID equality"),
            &transaction_id_input_program_snark_bits,
        )?;
    }

    let inner_snark_input =
        <N::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::merge_many(cs.ns(|| "inner_snark_input"), &[
            ledger_digest_fe,
            serial_number_fe,
            commitment_and_encrypted_record_hash_fe,
            program_id_fe,
            value_balance_fe,
            memo_fe,
            network_id_fe,
            transaction_id_fe_inner_snark,
        ])?;

    // ************************************************************************
    // Verify the inner circuit proof.
    // ************************************************************************

    let inner_snark_vk = <N::InnerSNARKGadget as SNARKVerifierGadget<_>>::VerificationKeyGadget::alloc(
        &mut cs.ns(|| "Allocate inner circuit verifying key"),
        || Ok(&private.inner_snark_vk),
    )?;

    let inner_snark_proof = <N::InnerSNARKGadget as SNARKVerifierGadget<_>>::ProofGadget::alloc(
        &mut cs.ns(|| "Allocate inner circuit proof"),
        || Ok(&private.inner_snark_proof),
    )?;

    N::InnerSNARKGadget::check_verify(
        &mut cs.ns(|| "Check that the inner circuit proof is satisfied"),
        &inner_snark_vk,
        &inner_snark_input,
        &inner_snark_proof,
    )?;

    // ************************************************************************
    // Verify each circuit exist in declared program and verify their proofs.
    // ************************************************************************
    {
        let cs = &mut cs.ns(|| "Check execution for program");

        let program_circuit_verifying_key =
            <N::ProgramSNARKGadget as SNARKVerifierGadget<_>>::VerificationKeyGadget::alloc(
                &mut cs.ns(|| "Allocate program circuit verifying key"),
                || Ok(&private.program_execution.verifying_key),
            )?;

        // Check that the program ID is derived correctly.
        {
            // Verify that the claimed circuit ID is a valid Merkle path in the program circuit tree.
            let program_circuit_verifying_key_bits = program_circuit_verifying_key
                .to_minimal_bits(cs.ns(|| "alloc_program_circuit_verifying_key_field_elements"))?;

            let claimed_circuit_id = program_circuit_id_crh.check_evaluation_gadget_on_bits(
                &mut cs.ns(|| "Compute circuit ID"),
                program_circuit_verifying_key_bits,
            )?;

            let claimed_circuit_id_bytes =
                claimed_circuit_id.to_bytes(&mut cs.ns(|| "Convert death circuit ID to bytes"))?;

            let program_path_gadget = MerklePathGadget::<_, N::ProgramCircuitsTreeCRHGadget, _>::alloc(
                &mut cs.ns(|| "Declare program path for circuit"),
                || Ok(&private.program_execution.program_path),
            )?;

            let claimed_program_id = program_path_gadget.calculate_root(
                &mut cs.ns(|| "calculate_program_id"),
                &program_circuits_tree_crh,
                claimed_circuit_id_bytes,
            )?;

            let claimed_program_id_bytes =
                claimed_program_id.to_bytes(&mut cs.ns(|| "Convert claimed program ID to bytes"))?;

            let given_program_id = UInt8::alloc_vec(
                &mut cs.ns(|| "Allocate given program ID"),
                &private.program_execution.program_id.to_bytes_le()?[..],
            )?;
            let given_program_id_bytes =
                given_program_id.to_bytes(&mut cs.ns(|| "Convert given program ID to bytes"))?;

            claimed_program_id_bytes.enforce_equal(
                &mut cs.ns(|| "Check that declared and computed program IDs are equal"),
                &given_program_id_bytes,
            )?;
        }

        // Verify the proof.

        let position_fe = <N::ProgramSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc_constant(
            &mut cs.ns(|| "Allocate position"),
            || Ok(vec![N::InnerScalarField::from(0u128)]),
        )?;
        let program_input = position_fe.merge(cs.ns(|| "Allocate program input"), &transaction_id_fe_program_snark)?;

        let program_circuit_proof = <N::ProgramSNARKGadget as SNARKVerifierGadget<_>>::ProofGadget::alloc(
            &mut cs.ns(|| "Allocate program circuit proof"),
            || Ok(&private.program_execution.proof),
        )?;

        N::ProgramSNARKGadget::check_verify(
            &mut cs.ns(|| "Check that the program proof is satisfied"),
            &program_circuit_verifying_key,
            &program_input,
            &program_circuit_proof,
        )?;
    }

    // ********************************************************************

    // ********************************************************************
    // Check that the inner circuit ID is derived correctly.
    // ********************************************************************

    let inner_snark_vk_bits = inner_snark_vk.to_minimal_bits(&mut cs.ns(|| "Convert inner snark vk to bits"))?;

    let given_inner_circuit_id =
        <N::InnerCircuitIDCRHGadget as CRHGadget<_, N::OuterScalarField>>::OutputGadget::alloc_input(
            &mut cs.ns(|| "Inner circuit ID"),
            || Ok(inner_circuit_id),
        )?;

    let candidate_inner_circuit_id = inner_circuit_id_crh
        .check_evaluation_gadget_on_bits(&mut cs.ns(|| "Compute inner circuit ID"), inner_snark_vk_bits)?;

    candidate_inner_circuit_id.enforce_equal(
        &mut cs.ns(|| "Check that declared and computed inner circuit IDs are equal"),
        &given_inner_circuit_id,
    )?;

    Ok(())
}

fn alloc_inner_snark_field_element<
    N: Network,
    V: ToConstraintField<N::InnerScalarField> + ?Sized,
    CS: ConstraintSystem<N::OuterScalarField>,
>(
    cs: &mut CS,
    var: &V,
    name: &str,
) -> Result<<N::InnerSNARKGadget as SNARKVerifierGadget<N::InnerSNARK>>::InputGadget, SynthesisError> {
    let field_elements = var.to_field_elements().map_err(|_| SynthesisError::AssignmentMissing)?;
    <N::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc(
        cs.ns(|| format!("alloc_field_element_{}", name)),
        || Ok(field_elements),
    )
}

fn alloc_inner_snark_input_field_element<
    'a,
    N: Network,
    V: ToConstraintField<N::InnerScalarField>,
    CS: ConstraintSystem<N::OuterScalarField>,
>(
    cs: &mut CS,
    var: &V,
    name: &str,
) -> Result<<N::InnerSNARKGadget as SNARKVerifierGadget<N::InnerSNARK>>::InputGadget, SynthesisError> {
    let field_elements = var.to_field_elements().map_err(|_| SynthesisError::AssignmentMissing)?;
    // allocate the field elements one by one
    let mut input_gadgets = Vec::with_capacity(field_elements.len());
    for (j, field_element) in field_elements.iter().enumerate() {
        input_gadgets.push(
            <N::InnerSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc_input(
                cs.ns(|| format!("alloc_input_field_element_{}_{}", name, j)),
                || Ok(vec![(*field_element).clone()]),
            )?,
        )
    }
    <N::InnerSNARKGadget as SNARKVerifierGadget<N::InnerSNARK>>::InputGadget::merge_many(
        cs.ns(|| format!("alloc_input_field_element_{}_merge", name)),
        &input_gadgets,
    )
}

fn alloc_program_snark_field_element<
    N: Network,
    V: ToConstraintField<N::InnerScalarField>,
    CS: ConstraintSystem<N::OuterScalarField>,
>(
    cs: &mut CS,
    var: &V,
    name: &str,
) -> Result<<N::ProgramSNARKGadget as SNARKVerifierGadget<N::ProgramSNARK>>::InputGadget, SynthesisError> {
    let field_elements = var.to_field_elements().map_err(|_| SynthesisError::AssignmentMissing)?;
    <N::ProgramSNARKGadget as SNARKVerifierGadget<_>>::InputGadget::alloc(
        cs.ns(|| format!("alloc_field_element_{}", name)),
        || Ok(field_elements),
    )
}
