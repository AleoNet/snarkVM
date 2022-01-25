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

use core::borrow::Borrow;

use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    fields::FpGadget,
    traits::alloc::AllocGadget,
    AllocBytesGadget,
    Boolean,
    EqGadget,
    PrepareGadget,
    ToBitsLEGadget,
    ToBytesGadget,
    ToConstraintFieldGadget,
    ToMinimalBitsGadget,
    UInt8,
};
use snarkvm_polycommit::PCCheckVar;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use crate::{
    constraints::{verifier::MarlinVerificationGadget, verifier_key::PreparedCircuitVerifyingKeyVar},
    marlin::{CircuitVerifyingKey, MarlinMode},
    FiatShamirRng,
    FiatShamirRngVar,
    PolynomialCommitment,
    Vec,
};
use snarkvm_algorithms::crypto_hash::PoseidonDefaultParametersField;
use snarkvm_utilities::{marker::PhantomData, FromBytes};

/// The circuit verifying key gadget
pub struct CircuitVerifyingKeyVar<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
> {
    /// The original key
    pub origin_verifier_key: CircuitVerifyingKey<TargetField, BaseField, PC, MM>,
    /// The size of domain h
    pub constraint_domain_size: u64,
    /// The size of domain k
    pub non_zero_domain_size: u64,
    /// The size of domain h in constraint form
    pub constraint_domain_size_gadget: FpGadget<BaseField>,
    /// The size of domain k in constraint form
    pub non_zero_domain_size_gadget: FpGadget<BaseField>,
    /// The circuit commitments in constraint form
    pub index_comms: Vec<PCG::CommitmentVar>,
    /// The verifying key in constraint form
    pub verifier_key: PCG::VerifierKeyVar,
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
> Clone for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
{
    fn clone(&self) -> Self {
        Self {
            origin_verifier_key: self.origin_verifier_key.clone(),
            constraint_domain_size: self.constraint_domain_size,
            non_zero_domain_size: self.non_zero_domain_size,
            constraint_domain_size_gadget: self.constraint_domain_size_gadget.clone(),
            non_zero_domain_size_gadget: self.non_zero_domain_size_gadget.clone(),
            index_comms: self.index_comms.clone(),
            verifier_key: self.verifier_key.clone(),
        }
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
> CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
{
    /// Returns an iterator of the circuit commitments.
    pub fn iter(&self) -> impl Iterator<Item = &PCG::CommitmentVar> {
        self.index_comms.iter()
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
> AllocGadget<CircuitVerifyingKey<TargetField, BaseField, PC, MM>, BaseField>
    for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
{
    #[inline]
    fn alloc_constant<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<CircuitVerifyingKey<TargetField, BaseField, PC, MM>>,
    {
        let tmp = value_gen()?;
        let ivk = tmp.borrow();

        let mut index_comms = Vec::<PCG::CommitmentVar>::new();
        for (i, index_comm) in ivk.circuit_commitments.iter().enumerate() {
            index_comms.push(PCG::CommitmentVar::alloc_constant(
                cs.ns(|| format!("index_comm_{}", i)),
                || Ok(index_comm),
            )?);
        }

        // `alloc_constant` regardless of the mode.
        let verifier_key = PCG::VerifierKeyVar::alloc_constant(cs.ns(|| "verifier_key"), || Ok(&ivk.verifier_key))?;

        let constraint_domain = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_domain = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let constraint_domain_size_gadget = FpGadget::<BaseField>::alloc_constant(cs.ns(|| "constraint_domain_size_gadget"), || {
            Ok(BaseField::from(constraint_domain.size() as u128))
        })?;
        let non_zero_domain_size_gadget = FpGadget::<BaseField>::alloc_constant(cs.ns(|| "non_zero_domain_size_gadget"), || {
            Ok(BaseField::from(non_zero_domain.size() as u128))
        })?;

        Ok(CircuitVerifyingKeyVar {
            origin_verifier_key: (*ivk).clone(),
            constraint_domain_size: constraint_domain.size() as u64,
            non_zero_domain_size: non_zero_domain.size() as u64,
            constraint_domain_size_gadget,
            non_zero_domain_size_gadget,
            index_comms,
            verifier_key,
        })
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<CircuitVerifyingKey<TargetField, BaseField, PC, MM>>,
    {
        let tmp = value_gen()?;
        let ivk = tmp.borrow();

        let index_comms: Vec<_> = ivk
            .circuit_commitments
            .iter()
            .enumerate()
            .map(|(i, index_comm)| PCG::CommitmentVar::alloc(cs.ns(|| format!("index_comm_{}", i)), || Ok(index_comm)))
            .collect::<Result<_, _>>()?;

        // `alloc_constant` regardless of the mode.
        // TODO(pratyush): investigate if this can be alloc_constant or not.
        // (I think it cannot).
        let verifier_key = PCG::VerifierKeyVar::alloc(cs.ns(|| "verifier_key"), || Ok(&ivk.verifier_key))?;

        let constraint_domain = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_domain = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let constraint_domain_size_gadget = FpGadget::<BaseField>::alloc(cs.ns(|| "constraint_domain_size_gadget"), || {
            Ok(BaseField::from(constraint_domain.size() as u128))
        })?;
        let non_zero_domain_size_gadget = FpGadget::<BaseField>::alloc(cs.ns(|| "non_zero_domain_size_gadget"), || {
            Ok(BaseField::from(non_zero_domain.size() as u128))
        })?;

        Ok(CircuitVerifyingKeyVar {
            origin_verifier_key: (*ivk).clone(),
            constraint_domain_size: constraint_domain.size() as u64,
            non_zero_domain_size: non_zero_domain.size() as u64,
            constraint_domain_size_gadget,
            non_zero_domain_size_gadget,
            index_comms,
            verifier_key,
        })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<CircuitVerifyingKey<TargetField, BaseField, PC, MM>>,
    {
        let tmp = value_gen()?;
        let ivk = tmp.borrow();

        let index_comms: Vec<_> = ivk
            .circuit_commitments
            .iter()
            .enumerate()
            .map(|(i, index_comm)| {
                PCG::CommitmentVar::alloc_input(cs.ns(|| format!("index_comm_{}", i)), || Ok(index_comm))
            })
            .collect::<Result<_, _>>()?;

        // `alloc_constant` regardless of the mode.
        // TODO(pratyush): investigate if this can be alloc_constant or not.
        // (I think it cannot).
        let verifier_key = PCG::VerifierKeyVar::alloc_input(cs.ns(|| "verifier_key"), || Ok(&ivk.verifier_key))?;

        let constraint_domain = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let non_zero_domain = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let constraint_domain_size_gadget = FpGadget::<BaseField>::alloc_input(cs.ns(|| "constraint_domain_size_gadget"), || {
            Ok(BaseField::from(constraint_domain.size() as u128))
        })?;
        let non_zero_domain_size_gadget = FpGadget::<BaseField>::alloc_input(cs.ns(|| "non_zero_domain_size_gadget"), || {
            Ok(BaseField::from(non_zero_domain.size() as u128))
        })?;

        Ok(CircuitVerifyingKeyVar {
            origin_verifier_key: (*ivk).clone(),
            constraint_domain_size: constraint_domain.size() as u64,
            non_zero_domain_size: non_zero_domain.size() as u64,
            constraint_domain_size_gadget,
            non_zero_domain_size_gadget,
            index_comms,
            verifier_key,
        })
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
> ToConstraintFieldGadget<BaseField> for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
{
    fn to_constraint_field<CS: ConstraintSystem<BaseField>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<FpGadget<BaseField>>, SynthesisError> {
        let mut res = Vec::new();
        res.append(
            &mut self
                .constraint_domain_size_gadget
                .to_constraint_field(cs.ns(|| "constraint_domain_size_gadget"))?,
        );
        res.append(
            &mut self
                .non_zero_domain_size_gadget
                .to_constraint_field(cs.ns(|| "non_zero_domain_size_gadget"))?,
        );
        for (i, comm) in self.index_comms.iter().enumerate() {
            res.append(&mut comm.to_constraint_field(cs.ns(|| format!("index_comm_{}", i)))?);
        }

        // Intentionally skip the PC verifier key

        Ok(res)
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
> ToMinimalBitsGadget<BaseField> for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
{
    fn to_minimal_bits<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
        let mut constraint_domain_size_booleans = self.constraint_domain_size_gadget.to_bits_le(cs.ns(|| "constraint_domain_size"))?;
        constraint_domain_size_booleans.truncate(64);

        let mut non_zero_domain_size_booleans = self.non_zero_domain_size_gadget.to_bits_le(cs.ns(|| "non_zero_domain_size"))?;
        non_zero_domain_size_booleans.truncate(64);

        // A sanity check that the sizes of constraint_domain and non_zero_domain are smaller than u64.
        {
            let constraint_domain_size_reconstructed =
                Boolean::le_bits_to_fp_var(cs.ns(|| "reconstruct constraint_domain_size"), &constraint_domain_size_booleans)?;
            let non_zero_domain_size_reconstructed =
                Boolean::le_bits_to_fp_var(cs.ns(|| "reconstruct non_zero_domain_size"), &non_zero_domain_size_booleans)?;

            constraint_domain_size_reconstructed.enforce_equal(cs.ns(|| "check constraint_domain_size"), &self.constraint_domain_size_gadget)?;
            non_zero_domain_size_reconstructed.enforce_equal(cs.ns(|| "check non_zero_domain_size"), &self.non_zero_domain_size_gadget)?;
        }

        let index_comms_booleans = self.index_comms.to_minimal_bits(cs.ns(|| "index_comms"))?;

        Ok([constraint_domain_size_booleans, non_zero_domain_size_booleans, index_comms_booleans].concat())
    }
}

impl<TargetField, BaseField, PC, PCG, PR, R, MM>
    PrepareGadget<PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, PR, R, MM>, BaseField>
    for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
where
    TargetField: PrimeField,
    BaseField: PrimeField + PoseidonDefaultParametersField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PR: FiatShamirRng<TargetField, BaseField>,
    R: FiatShamirRngVar<TargetField, BaseField, PR>,
    MM: MarlinMode,
{
    /// Returns an instance of a `PreparedCircuitVerifyingKeyGadget`.
    fn prepare<CS: ConstraintSystem<BaseField>>(
        &self,
        mut cs: CS,
    ) -> Result<PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, PR, R, MM>, SynthesisError> {
        let mut fs_rng = R::new(cs.ns(|| "Init rng"));
        let protocol_bytes =
            UInt8::constant_vec(MarlinVerificationGadget::<TargetField, BaseField, PC, PCG, MM>::PROTOCOL_NAME);
        fs_rng.absorb_bytes(cs.ns(|| "absorb protocol name"), &protocol_bytes)?;

        let comm_fe = self
            .index_comms
            .iter()
            .enumerate()
            .flat_map(|(i, c)| {
                c.to_constraint_field(cs.ns(|| format!("to_constraint_field {}", i)))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        fs_rng.absorb_native_field_elements(cs.ns(|| "absorb index commitments"), &comm_fe)?;

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentVar>::new();
        for (i, comm) in self.index_comms.iter().enumerate() {
            prepared_index_comms.push(comm.prepare(cs.ns(|| format!("prepare_{}", i)))?);
        }

        // instead of running the prepare algorithm, allocate the constant version.
        let prepared_verifier_key = self.verifier_key.prepare(cs.ns(|| "Prepare PC"))?;

        Ok(PreparedCircuitVerifyingKeyVar {
            constraint_domain_size: self.constraint_domain_size,
            non_zero_domain_size: self.non_zero_domain_size,
            constraint_domain_size_gadget: self.constraint_domain_size_gadget.clone(),
            non_zero_domain_size_gadget: self.non_zero_domain_size_gadget.clone(),
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
            pr: PhantomData,
        })
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
> ToBytesGadget<BaseField> for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
{
    fn to_bytes<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut res = Vec::<UInt8>::new();

        res.append(&mut self.constraint_domain_size_gadget.to_bytes(cs.ns(|| "constraint_domain_size_gadget"))?);
        res.append(&mut self.non_zero_domain_size_gadget.to_bytes(cs.ns(|| "non_zero_domain_size_gadget"))?);
        res.append(&mut self.verifier_key.to_bytes(cs.ns(|| "verifier_key"))?);

        for (i, comm) in self.index_comms.iter().enumerate() {
            res.append(&mut comm.to_bytes(cs.ns(|| format!("commitment_{}", i)))?);
        }

        Ok(res)
    }

    fn to_bytes_strict<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut res = Vec::<UInt8>::new();
        res.append(&mut self.constraint_domain_size_gadget.to_bytes(cs.ns(|| "constraint_domain_size_gadget"))?);
        res.append(&mut self.non_zero_domain_size_gadget.to_bytes(cs.ns(|| "non_zero_domain_size_gadget"))?);
        res.append(&mut self.verifier_key.to_bytes(cs.ns(|| "verifier_key"))?);

        for (i, comm) in self.index_comms.iter().enumerate() {
            res.append(&mut comm.to_bytes(cs.ns(|| format!("commitment_{}", i)))?);
        }

        Ok(res)
    }
}

impl<TargetField, BaseField, PC, PCG, MM> AllocBytesGadget<Vec<u8>, BaseField>
    for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, MM>
where
    TargetField: PrimeField,
    BaseField: PrimeField + PoseidonDefaultParametersField,
    PC: PolynomialCommitment<TargetField, BaseField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    MM: MarlinMode,
{
    #[inline]
    fn alloc_bytes<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<u8>>,
    {
        value_gen().and_then(|vk_bytes| {
            let circuit_vk: CircuitVerifyingKey<TargetField, BaseField, PC, MM> =
                FromBytes::read_le(&vk_bytes.borrow()[..])?;

            CircuitVerifyingKeyVar::<TargetField, BaseField, PC, PCG, MM>::alloc(cs.ns(|| "unprepared_vk"), || {
                Ok(circuit_vk)
            })
        })
    }

    #[inline]
    fn alloc_input_bytes<FN, T, CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        value_gen: FN,
    ) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Vec<u8>>,
    {
        value_gen().and_then(|vk_bytes| {
            let circuit_vk: CircuitVerifyingKey<_, _, _, _> = FromBytes::read_le(&vk_bytes.borrow()[..])?;

            CircuitVerifyingKeyVar::<TargetField, BaseField, PC, PCG, MM>::alloc_input(
                cs.ns(|| "unprepared_vk"),
                || Ok(circuit_vk),
            )
        })
    }
}

#[cfg(test)]
mod test {
    use core::ops::MulAssign;

    use blake2::Blake2s;

    use snarkvm_curves::{
        bls12_377::{Bls12_377, Fq, Fr},
        bw6_761::BW6_761,
    };
    use snarkvm_gadgets::{curves::bls12_377::PairingGadget as Bls12_377PairingGadget, traits::eq::EqGadget};
    use snarkvm_polycommit::sonic_pc::{sonic_kzg10::SonicKZG10Gadget, SonicKZG10};
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::rand::{test_rng, UniformRand};

    use crate::{
        fiat_shamir::FiatShamirChaChaRng,
        marlin::{tests::Circuit, MarlinSNARK, MarlinTestnet1Mode},
    };

    use super::*;

    type MultiPC = SonicKZG10<Bls12_377>;
    type MarlinInst = MarlinSNARK<Fr, Fq, MultiPC, FiatShamirChaChaRng<Fr, Fq, Blake2s>, MarlinTestnet1Mode>;

    type MultiPCVar = SonicKZG10Gadget<Bls12_377, BW6_761, Bls12_377PairingGadget>;

    #[test]
    fn test_alloc() {
        let rng = &mut test_rng();

        let cs = &mut TestConstraintSystem::<Fq>::new();

        let num_constraints = 25;
        let num_variables = 25;

        // Construct the circuit verifier key.
        let max_degree = crate::ahp::AHPForR1CS::<Fr, MarlinTestnet1Mode>::max_degree(100, 25, 100).unwrap();
        let universal_srs = MarlinInst::universal_setup(max_degree, rng).unwrap();

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let mut c = a;
        c.mul_assign(&b);
        let mut d = c;
        d.mul_assign(&b);

        let circ = Circuit {
            a: Some(a),
            b: Some(b),
            num_constraints,
            num_variables,
        };

        let (_circuit_pk, circuit_vk) = MarlinInst::circuit_setup(&universal_srs, &circ).unwrap();

        // Allocate the circuit vk gadget.
        let circuit_vk_gadget =
            CircuitVerifyingKeyVar::<_, _, _, MultiPCVar, _>::alloc(cs.ns(|| "alloc_vk"), || Ok(circuit_vk.clone()))
                .unwrap();

        // Enforce that the native vk and vk gadget elements are equivalent.

        for (i, (commitment, commitment_gadget)) in circuit_vk
            .circuit_commitments
            .iter()
            .zip(circuit_vk_gadget.index_comms)
            .enumerate()
        {
            let expected_commitment_gadget = <MultiPCVar as PCCheckVar<_, _, _>>::CommitmentVar::alloc(
                cs.ns(|| format!("alloc_commitment_{}", i)),
                || Ok(commitment),
            )
            .unwrap();

            commitment_gadget
                .comm
                .enforce_equal(
                    cs.ns(|| format!("enforce_equal_comm_{}", i)),
                    &expected_commitment_gadget.comm,
                )
                .unwrap();
        }

        assert!(cs.is_satisfied());
    }
}
