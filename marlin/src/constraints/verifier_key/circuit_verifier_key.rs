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

use crate::{marlin::CircuitVerifyingKey, PolynomialCommitment};

use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    fields::FpGadget,
    utilities::{alloc::AllocGadget, uint::UInt8, ToBytesGadget},
};
use snarkvm_polycommit::PCCheckVar;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use core::borrow::Borrow;

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
