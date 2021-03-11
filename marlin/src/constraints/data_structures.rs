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
    constraints::verifier::MarlinVerificationGadget as MarlinVerifierVar,
    fiat_shamir::{constraints::FiatShamirRngVar, FiatShamirRng},
    marlin::{CircuitVerifyingKey, PreparedCircuitVerifyingKey, Proof},
    PhantomData,
    String,
    ToString,
    Vec,
};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    fields::FpGadget,
    traits::{
        fields::{FieldGadget, ToConstraintFieldGadget},
        utilities::{alloc::AllocGadget, uint::UInt8},
    },
    utilities::ToBytesGadget,
};
use snarkvm_nonnative::NonNativeFieldVar;
use snarkvm_polycommit::{
    constraints::{PCCheckVar, PrepareGadget},
    PolynomialCommitment,
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_utilities::{to_bytes, ToBytes};

use hashbrown::HashMap;
use std::borrow::Borrow;

/// Syntactic sugar for the universal SRS in this context.
pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F>>::UniversalParams;

/// The circuit verifying key gadget
pub struct CircuitVerifyingKeyVar<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> {
    /// The size of domain h
    pub domain_h_size: u64,
    /// The size of domain k
    pub domain_k_size: u64,
    /// The size of domain h in constraint form
    pub domain_h_size_gadget: FpGadget<BaseField>,
    /// The size of domain k in constraint form
    pub domain_k_size_gadget: FpGadget<BaseField>,
    /// The circuit commitments in constraint form
    pub index_comms: Vec<PCG::CommitmentVar>,
    /// The verifying key in constraint form
    pub verifier_key: PCG::VerifierKeyVar,
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> AllocGadget<CircuitVerifyingKey<TargetField, PC>, BaseField>
    for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>
{
    #[inline]
    fn alloc_constant<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<CircuitVerifyingKey<TargetField, PC>>,
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

        let verifier_key = PCG::VerifierKeyVar::alloc_constant(cs.ns(|| "verifier_key"), || Ok(&ivk.verifier_key))?;

        let domain_h = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_size_gadget = FpGadget::<BaseField>::alloc_constant(cs.ns(|| "domain_h_size_gadget"), || {
            Ok(BaseField::from(domain_h.size() as u128))
        })?;
        let domain_k_size_gadget = FpGadget::<BaseField>::alloc_constant(cs.ns(|| "domain_k_size_gadget"), || {
            Ok(BaseField::from(domain_k.size() as u128))
        })?;

        Ok(CircuitVerifyingKeyVar {
            domain_h_size: domain_h.size() as u64,
            domain_k_size: domain_k.size() as u64,
            domain_h_size_gadget,
            domain_k_size_gadget,
            index_comms,
            verifier_key,
        })
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<CircuitVerifyingKey<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let ivk = tmp.borrow();

        let mut index_comms = Vec::<PCG::CommitmentVar>::new();
        for (i, index_comm) in ivk.circuit_commitments.iter().enumerate() {
            index_comms.push(PCG::CommitmentVar::alloc(
                cs.ns(|| format!("index_comm_{}", i)),
                || Ok(index_comm),
            )?);
        }

        let verifier_key = PCG::VerifierKeyVar::alloc(cs.ns(|| "verifier_key"), || Ok(&ivk.verifier_key))?;

        let domain_h = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_size_gadget = FpGadget::<BaseField>::alloc(cs.ns(|| "domain_h_size_gadget"), || {
            Ok(BaseField::from(domain_h.size() as u128))
        })?;
        let domain_k_size_gadget = FpGadget::<BaseField>::alloc(cs.ns(|| "domain_k_size_gadget"), || {
            Ok(BaseField::from(domain_k.size() as u128))
        })?;

        Ok(CircuitVerifyingKeyVar {
            domain_h_size: domain_h.size() as u64,
            domain_k_size: domain_k.size() as u64,
            domain_h_size_gadget,
            domain_k_size_gadget,
            index_comms,
            verifier_key,
        })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<CircuitVerifyingKey<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let ivk = tmp.borrow();

        let mut index_comms = Vec::<PCG::CommitmentVar>::new();
        for (i, index_comm) in ivk.circuit_commitments.iter().enumerate() {
            index_comms.push(PCG::CommitmentVar::alloc_input(
                cs.ns(|| format!("index_comm_{}", i)),
                || Ok(index_comm),
            )?);
        }

        let verifier_key = PCG::VerifierKeyVar::alloc_input(cs.ns(|| "verifier_key"), || Ok(&ivk.verifier_key))?;

        let domain_h = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = EvaluationDomain::<TargetField>::new(ivk.circuit_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_size_gadget = FpGadget::<BaseField>::alloc_input(cs.ns(|| "domain_h_size_gadget"), || {
            Ok(BaseField::from(domain_h.size() as u128))
        })?;
        let domain_k_size_gadget = FpGadget::<BaseField>::alloc_input(cs.ns(|| "domain_k_size_gadget"), || {
            Ok(BaseField::from(domain_k.size() as u128))
        })?;

        Ok(CircuitVerifyingKeyVar {
            domain_h_size: domain_h.size() as u64,
            domain_k_size: domain_k.size() as u64,
            domain_h_size_gadget,
            domain_k_size_gadget,
            index_comms,
            verifier_key,
        })
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> ToBytesGadget<BaseField> for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>
{
    fn to_bytes<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut res = Vec::<UInt8>::new();

        res.append(&mut self.domain_h_size_gadget.to_bytes(cs.ns(|| "domain_h_size_gadget"))?);
        res.append(&mut self.domain_k_size_gadget.to_bytes(cs.ns(|| "domain_k_size_gadget"))?);
        res.append(&mut self.verifier_key.to_bytes(cs.ns(|| "verifier_key"))?);

        for (i, comm) in self.index_comms.iter().enumerate() {
            res.append(&mut comm.to_bytes(cs.ns(|| format!("commitment_{}", i)))?);
        }

        Ok(res)
    }

    fn to_bytes_strict<CS: ConstraintSystem<BaseField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError> {
        let mut res = Vec::<UInt8>::new();

        res.append(&mut self.domain_h_size_gadget.to_bytes(cs.ns(|| "domain_h_size_gadget"))?);
        res.append(&mut self.domain_k_size_gadget.to_bytes(cs.ns(|| "domain_k_size_gadget"))?);
        res.append(&mut self.verifier_key.to_bytes(cs.ns(|| "verifier_key"))?);

        for (i, comm) in self.index_comms.iter().enumerate() {
            res.append(&mut comm.to_bytes(cs.ns(|| format!("commitment_{}", i)))?);
        }

        Ok(res)
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> Clone for CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>
{
    fn clone(&self) -> Self {
        Self {
            domain_h_size: self.domain_h_size,
            domain_k_size: self.domain_k_size,
            domain_h_size_gadget: self.domain_h_size_gadget.clone(),
            domain_k_size_gadget: self.domain_k_size_gadget.clone(),
            index_comms: self.index_comms.clone(),
            verifier_key: self.verifier_key.clone(),
        }
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>
{
    /// Returns an iterator of the circuit commitments.
    pub fn iter(&self) -> impl Iterator<Item = &PCG::CommitmentVar> {
        self.index_comms.iter()
    }
}

/// The prepared circuit verifying key gadget
pub struct PreparedCircuitVerifyingKeyVar<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PR: FiatShamirRng<TargetField, BaseField>,
    R: FiatShamirRngVar<TargetField, BaseField, PR>,
> {
    /// The size of domain h
    pub domain_h_size: u64,
    /// The size of domain k
    pub domain_k_size: u64,
    /// The size of domain h in constraint form
    pub domain_h_size_gadget: FpGadget<BaseField>,
    /// The size of domain k in constraint form
    pub domain_k_size_gadget: FpGadget<BaseField>,
    /// The prepared circuit commitments in constraint form
    pub prepared_index_comms: Vec<PCG::PreparedCommitmentVar>,
    /// The prepared verifying key in constraint form
    pub prepared_verifier_key: PCG::PreparedVerifierKeyVar,
    /// The Fiat-Shamir Rng
    pub fs_rng: R,

    pr: PhantomData<PR>,
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PR: FiatShamirRng<TargetField, BaseField>,
    R: FiatShamirRngVar<TargetField, BaseField, PR>,
> Clone for PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, PR, R>
{
    fn clone(&self) -> Self {
        PreparedCircuitVerifyingKeyVar {
            domain_h_size: self.domain_h_size,
            domain_k_size: self.domain_k_size,
            domain_h_size_gadget: self.domain_h_size_gadget.clone(),
            domain_k_size_gadget: self.domain_k_size_gadget.clone(),
            prepared_index_comms: self.prepared_index_comms.clone(),
            prepared_verifier_key: self.prepared_verifier_key.clone(),
            fs_rng: self.fs_rng.clone(),
            pr: PhantomData,
        }
    }
}

impl<TargetField, BaseField, PC, PCG, PR, R> PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, PR, R>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PR: FiatShamirRng<TargetField, BaseField>,
    R: FiatShamirRngVar<TargetField, BaseField, PR>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
{
    /// Returns an instance of a `PreparedCircuitVerifyingKeyGadget`.
    pub fn prepare<CS: ConstraintSystem<BaseField>>(
        mut cs: CS,
        vk: &CircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG>,
    ) -> Result<Self, SynthesisError> {
        let mut fs_rng_raw = PR::new();
        fs_rng_raw.absorb_bytes(&to_bytes![
            &MarlinVerifierVar::<TargetField, BaseField, PC, PCG>::PROTOCOL_NAME
        ]?);

        let index_vk_hash = {
            let mut vk_hash_rng = PR::new();

            let mut vk_elems = Vec::<BaseField>::new();
            vk.index_comms.iter().for_each(|index_comm| {
                vk_elems.append(
                    &mut index_comm
                        .to_constraint_field()
                        .unwrap()
                        .iter()
                        .map(|elem| elem.get_value().unwrap_or_default())
                        .collect(),
                );
            });
            vk_hash_rng.absorb_native_field_elements(&vk_elems);
            FpGadget::<BaseField>::alloc(cs.ns(|| "alloc_vk_hash"), || {
                Ok(vk_hash_rng.squeeze_native_field_elements(1)[0])
            })?
        };

        let fs_rng = {
            let mut fs_rng = R::constant(cs.ns(|| "fs_rng_raw"), &fs_rng_raw);
            fs_rng.absorb_native_field_elements(cs.ns(|| "absorb"), &[index_vk_hash])?;
            fs_rng
        };

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentVar>::new();
        for (i, comm) in vk.index_comms.iter().enumerate() {
            prepared_index_comms.push(PCG::PreparedCommitmentVar::prepare(
                cs.ns(|| format!("prepare_{}", i)),
                comm,
            )?);
        }

        let prepared_verifier_key = PCG::PreparedVerifierKeyVar::prepare(cs.ns(|| "prepare_last"), &vk.verifier_key)?;

        Ok(Self {
            domain_h_size: vk.domain_h_size,
            domain_k_size: vk.domain_k_size,
            domain_h_size_gadget: vk.domain_h_size_gadget.clone(),
            domain_k_size_gadget: vk.domain_k_size_gadget.clone(),
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
            pr: PhantomData,
        })
    }
}

impl<TargetField, BaseField, PC, PCG, PR, R> AllocGadget<PreparedCircuitVerifyingKey<TargetField, PC>, BaseField>
    for PreparedCircuitVerifyingKeyVar<TargetField, BaseField, PC, PCG, PR, R>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PR: FiatShamirRng<TargetField, BaseField>,
    R: FiatShamirRngVar<TargetField, BaseField, PR>,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
{
    #[inline]
    fn alloc_constant<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedCircuitVerifyingKey<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let obj = tmp.borrow();

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentVar>::new();
        for (i, index_comm) in obj.prepared_index_comms.iter().enumerate() {
            prepared_index_comms.push(PCG::PreparedCommitmentVar::alloc_constant(
                cs.ns(|| format!("alloc_constant_index_commitment_{}", i)),
                || Ok(index_comm),
            )?);
        }

        let prepared_verifier_key =
            PCG::PreparedVerifierKeyVar::alloc_constant(cs.ns(|| "alloc_constant_pvk"), || {
                Ok(&obj.prepared_verifier_key)
            })?;

        let mut vk_elems = Vec::<BaseField>::new();
        obj.orig_vk.circuit_commitments.iter().for_each(|index_comm| {
            vk_elems.append(&mut index_comm.to_field_elements().unwrap());
        });

        let index_vk_hash = {
            let mut vk_hash_rng = PR::new();

            vk_hash_rng.absorb_native_field_elements(&vk_elems);
            FpGadget::<BaseField>::alloc_constant(cs.ns(|| "alloc_constant_vk_hash"), || {
                Ok(vk_hash_rng.squeeze_native_field_elements(1)[0])
            })?
        };

        let mut fs_rng_raw = PR::new();
        fs_rng_raw.absorb_bytes(&to_bytes![
            &MarlinVerifierVar::<TargetField, BaseField, PC, PCG>::PROTOCOL_NAME
        ]?);

        let fs_rng = {
            let mut fs_rng = R::constant(cs.ns(|| "fs_rng_raw"), &fs_rng_raw);
            fs_rng.absorb_native_field_elements(cs.ns(|| "absorb"), &[index_vk_hash])?;
            fs_rng
        };

        let domain_h_size_gadget = FpGadget::<BaseField>::alloc_constant(cs.ns(|| "domain_h_size_gadget"), || {
            Ok(BaseField::from(obj.domain_h_size as u128))
        })?;
        let domain_k_size_gadget = FpGadget::<BaseField>::alloc_constant(cs.ns(|| "domain_k_size_gadget"), || {
            Ok(BaseField::from(obj.domain_k_size as u128))
        })?;

        Ok(Self {
            domain_h_size: obj.domain_h_size,
            domain_k_size: obj.domain_k_size,
            domain_h_size_gadget,
            domain_k_size_gadget,
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
            pr: PhantomData,
        })
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedCircuitVerifyingKey<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let obj = tmp.borrow();

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentVar>::new();
        for (i, index_comm) in obj.prepared_index_comms.iter().enumerate() {
            prepared_index_comms.push(PCG::PreparedCommitmentVar::alloc(
                cs.ns(|| format!("alloc_index_commitment_{}", i)),
                || Ok(index_comm),
            )?);
        }

        let prepared_verifier_key =
            PCG::PreparedVerifierKeyVar::alloc(cs.ns(|| "alloc_pvk"), || Ok(&obj.prepared_verifier_key))?;

        let mut vk_elems = Vec::<BaseField>::new();
        obj.orig_vk.circuit_commitments.iter().for_each(|index_comm| {
            vk_elems.append(&mut index_comm.to_field_elements().unwrap());
        });

        let index_vk_hash = {
            let mut vk_hash_rng = PR::new();

            vk_hash_rng.absorb_native_field_elements(&vk_elems);
            FpGadget::<BaseField>::alloc(cs.ns(|| "alloc_vk_hash"), || {
                Ok(vk_hash_rng.squeeze_native_field_elements(1)[0])
            })?
        };

        let mut fs_rng_raw = PR::new();
        fs_rng_raw.absorb_bytes(&to_bytes![
            &MarlinVerifierVar::<TargetField, BaseField, PC, PCG>::PROTOCOL_NAME
        ]?);

        let fs_rng = {
            let mut fs_rng = R::constant(cs.ns(|| "fs_rng_raw"), &fs_rng_raw);
            fs_rng.absorb_native_field_elements(cs.ns(|| "absorb"), &[index_vk_hash])?;
            fs_rng
        };

        let domain_h_size_gadget = FpGadget::<BaseField>::alloc(cs.ns(|| "domain_h_size_gadget"), || {
            Ok(BaseField::from(obj.domain_h_size as u128))
        })?;
        let domain_k_size_gadget = FpGadget::<BaseField>::alloc(cs.ns(|| "domain_k_size_gadget"), || {
            Ok(BaseField::from(obj.domain_k_size as u128))
        })?;

        Ok(Self {
            domain_h_size: obj.domain_h_size,
            domain_k_size: obj.domain_k_size,
            domain_h_size_gadget,
            domain_k_size_gadget,
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
            pr: PhantomData,
        })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedCircuitVerifyingKey<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let obj = tmp.borrow();

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentVar>::new();
        for (i, index_comm) in obj.prepared_index_comms.iter().enumerate() {
            prepared_index_comms.push(PCG::PreparedCommitmentVar::alloc_input(
                cs.ns(|| format!("alloc_input_index_commitment_{}", i)),
                || Ok(index_comm),
            )?);
        }

        let prepared_verifier_key =
            PCG::PreparedVerifierKeyVar::alloc_input(cs.ns(|| "alloc_input_pvk"), || Ok(&obj.prepared_verifier_key))?;

        let mut vk_elems = Vec::<BaseField>::new();
        obj.orig_vk.circuit_commitments.iter().for_each(|index_comm| {
            vk_elems.append(&mut index_comm.to_field_elements().unwrap());
        });

        let index_vk_hash = {
            let mut vk_hash_rng = PR::new();

            vk_hash_rng.absorb_native_field_elements(&vk_elems);
            FpGadget::<BaseField>::alloc_input(cs.ns(|| "alloc_input_vk_hash"), || {
                Ok(vk_hash_rng.squeeze_native_field_elements(1)[0])
            })?
        };

        let mut fs_rng_raw = PR::new();
        fs_rng_raw.absorb_bytes(&to_bytes![
            &MarlinVerifierVar::<TargetField, BaseField, PC, PCG>::PROTOCOL_NAME
        ]?);

        let fs_rng = {
            let mut fs_rng = R::constant(cs.ns(|| "fs_rng_raw"), &fs_rng_raw);
            fs_rng.absorb_native_field_elements(cs.ns(|| "absorb"), &[index_vk_hash])?;
            fs_rng
        };

        let domain_h_size_gadget = FpGadget::<BaseField>::alloc_input(cs.ns(|| "domain_h_size_gadget"), || {
            Ok(BaseField::from(obj.domain_h_size as u128))
        })?;
        let domain_k_size_gadget = FpGadget::<BaseField>::alloc_input(cs.ns(|| "domain_k_size_gadget"), || {
            Ok(BaseField::from(obj.domain_k_size as u128))
        })?;

        Ok(Self {
            domain_h_size: obj.domain_h_size,
            domain_k_size: obj.domain_k_size,
            domain_h_size_gadget,
            domain_k_size_gadget,
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
            pr: PhantomData,
        })
    }
}

/// The Marlin proof gadget
pub struct ProofVar<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> {
    /// The commitments
    pub commitments: Vec<Vec<PCG::CommitmentVar>>,
    /// The evaluations
    pub evaluations: HashMap<String, NonNativeFieldVar<TargetField, BaseField>>,
    /// The prover messages
    pub prover_messages: Vec<ProverMessageVar<TargetField, BaseField>>,
    /// The polynomial commitment batch proof
    pub pc_batch_proof: PCG::BatchLCProofVar,
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> ProofVar<TargetField, BaseField, PC, PCG>
{
    /// Instantiates a new instance of `ProofGadget`.
    pub fn new(
        commitments: Vec<Vec<PCG::CommitmentVar>>,
        evaluations: HashMap<String, NonNativeFieldVar<TargetField, BaseField>>,
        prover_messages: Vec<ProverMessageVar<TargetField, BaseField>>,
        pc_batch_proof: PCG::BatchLCProofVar,
    ) -> Self {
        Self {
            commitments,
            evaluations,
            prover_messages,
            pc_batch_proof,
        }
    }
}

impl<TargetField, BaseField, PC, PCG> AllocGadget<Proof<TargetField, PC>, BaseField>
    for ProofVar<TargetField, BaseField, PC, PCG>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PC::VerifierKey: ToConstraintField<BaseField>,
    PC::Commitment: ToConstraintField<BaseField>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
{
    #[inline]
    fn alloc_constant<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = tmp.borrow();

        let commitment_gadgets: Vec<Vec<PCG::CommitmentVar>> = commitments
            .iter()
            .map(|lst| {
                lst.iter()
                    .enumerate()
                    .map(|(i, comm)| {
                        PCG::CommitmentVar::alloc_constant(cs.ns(|| format!("alloc_constant_commitment_{}", i)), || {
                            Ok(comm)
                        })
                        .unwrap()
                    })
                    .collect()
            })
            .collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldVar<TargetField, BaseField>> = evaluations
            .iter()
            .enumerate()
            .map(|(i, eval)| {
                NonNativeFieldVar::alloc_constant(cs.ns(|| format!("alloc_constant_evaluations_{}", i)), || Ok(eval))
                    .unwrap()
            })
            .collect();

        let prover_message_gadgets: Vec<ProverMessageVar<TargetField, BaseField>> = prover_messages
            .iter()
            .enumerate()
            .map(|(i, msg)| {
                let field_elements: Vec<NonNativeFieldVar<TargetField, BaseField>> = msg
                    .field_elements
                    .iter()
                    .enumerate()
                    .map(|(j, elem)| {
                        NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_constant_message_{}_{}", i, j)), || Ok(elem))
                            .unwrap()
                    })
                    .collect();

                ProverMessageVar { field_elements }
            })
            .collect();

        let pc_batch_proof = PCG::BatchLCProofVar::alloc_constant(cs.ns(|| "alloc_constant_proof"), || Ok(pc_proof))?;

        let mut evaluation_gadgets = HashMap::<String, NonNativeFieldVar<TargetField, BaseField>>::new();

        const ALL_POLYNOMIALS: [&str; 10] = [
            "a_denom",
            "b_denom",
            "c_denom",
            "g_1",
            "g_2",
            "t",
            "vanishing_poly_h_alpha",
            "vanishing_poly_h_beta",
            "vanishing_poly_k_gamma",
            "z_b",
        ];

        for (s, eval) in ALL_POLYNOMIALS.iter().zip(evaluation_gadgets_vec.iter()) {
            evaluation_gadgets.insert(s.to_string(), (*eval).clone());
        }

        Ok(ProofVar {
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        })
    }

    #[inline]
    fn alloc<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = tmp.borrow();

        let commitment_gadgets: Vec<Vec<PCG::CommitmentVar>> = commitments
            .iter()
            .map(|lst| {
                lst.iter()
                    .enumerate()
                    .map(|(i, comm)| {
                        PCG::CommitmentVar::alloc(cs.ns(|| format!("alloc_commitment_{}", i)), || Ok(comm)).unwrap()
                    })
                    .collect()
            })
            .collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldVar<TargetField, BaseField>> = evaluations
            .iter()
            .enumerate()
            .map(|(i, eval)| {
                NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_evaluations_{}", i)), || Ok(eval)).unwrap()
            })
            .collect();

        let prover_message_gadgets: Vec<ProverMessageVar<TargetField, BaseField>> = prover_messages
            .iter()
            .enumerate()
            .map(|(i, msg)| {
                let field_elements: Vec<NonNativeFieldVar<TargetField, BaseField>> = msg
                    .field_elements
                    .iter()
                    .enumerate()
                    .map(|(j, elem)| {
                        NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_prover_message_{}_{}", i, j)), || Ok(elem))
                            .unwrap()
                    })
                    .collect();
                ProverMessageVar { field_elements }
            })
            .collect();

        let pc_batch_proof = PCG::BatchLCProofVar::alloc(cs.ns(|| "alloc_proof"), || Ok(pc_proof))?;

        let mut evaluation_gadgets = HashMap::<String, NonNativeFieldVar<TargetField, BaseField>>::new();

        const ALL_POLYNOMIALS: [&str; 10] = [
            "a_denom",
            "b_denom",
            "c_denom",
            "g_1",
            "g_2",
            "t",
            "vanishing_poly_h_alpha",
            "vanishing_poly_h_beta",
            "vanishing_poly_k_gamma",
            "z_b",
        ];

        for (s, eval) in ALL_POLYNOMIALS.iter().zip(evaluation_gadgets_vec.iter()) {
            evaluation_gadgets.insert(s.to_string(), (*eval).clone());
        }

        Ok(ProofVar {
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        })
    }

    #[inline]
    fn alloc_input<FN, T, CS: ConstraintSystem<BaseField>>(mut cs: CS, value_gen: FN) -> Result<Self, SynthesisError>
    where
        FN: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<TargetField, PC>>,
    {
        let tmp = value_gen()?;
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = tmp.borrow();

        let commitment_gadgets: Vec<Vec<PCG::CommitmentVar>> = commitments
            .iter()
            .map(|lst| {
                lst.iter()
                    .enumerate()
                    .map(|(i, comm)| {
                        PCG::CommitmentVar::alloc_input(cs.ns(|| format!("alloc_input_commitment_{}", i)), || Ok(comm))
                            .unwrap()
                    })
                    .collect()
            })
            .collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldVar<TargetField, BaseField>> = evaluations
            .iter()
            .enumerate()
            .map(|(i, eval)| {
                NonNativeFieldVar::alloc_input(cs.ns(|| format!("alloc_input_evaluations_{}", i)), || Ok(eval)).unwrap()
            })
            .collect();

        let prover_message_gadgets: Vec<ProverMessageVar<TargetField, BaseField>> = prover_messages
            .iter()
            .enumerate()
            .map(|(i, msg)| {
                let field_elements: Vec<NonNativeFieldVar<TargetField, BaseField>> = msg
                    .field_elements
                    .iter()
                    .enumerate()
                    .map(|(j, elem)| {
                        NonNativeFieldVar::alloc(cs.ns(|| format!("alloc_input_prover_message_{}_{}", i, j)), || {
                            Ok(elem)
                        })
                        .unwrap()
                    })
                    .collect();

                ProverMessageVar { field_elements }
            })
            .collect();

        let pc_batch_proof = PCG::BatchLCProofVar::alloc_input(cs.ns(|| "alloc_input_proof"), || Ok(pc_proof))?;

        let mut evaluation_gadgets = HashMap::<String, NonNativeFieldVar<TargetField, BaseField>>::new();

        const ALL_POLYNOMIALS: [&str; 10] = [
            "a_denom",
            "b_denom",
            "c_denom",
            "g_1",
            "g_2",
            "t",
            "vanishing_poly_h_alpha",
            "vanishing_poly_h_beta",
            "vanishing_poly_k_gamma",
            "z_b",
        ];

        for (s, eval) in ALL_POLYNOMIALS.iter().zip(evaluation_gadgets_vec.iter()) {
            evaluation_gadgets.insert(s.to_string(), (*eval).clone());
        }

        Ok(ProofVar {
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        })
    }
}

impl<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
> Clone for ProofVar<TargetField, BaseField, PC, PCG>
{
    fn clone(&self) -> Self {
        ProofVar {
            commitments: self.commitments.clone(),
            evaluations: self.evaluations.clone(),
            prover_messages: self.prover_messages.clone(),
            pc_batch_proof: self.pc_batch_proof.clone(),
        }
    }
}

/// The prover message gadget
#[repr(transparent)]
pub struct ProverMessageVar<TargetField: PrimeField, BaseField: PrimeField> {
    /// The field elements comprising the message in nonnative field gadgets.
    pub field_elements: Vec<NonNativeFieldVar<TargetField, BaseField>>,
}

impl<TargetField: PrimeField, BaseField: PrimeField> Clone for ProverMessageVar<TargetField, BaseField> {
    fn clone(&self) -> Self {
        ProverMessageVar {
            field_elements: self.field_elements.clone(),
        }
    }
}
