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

use snarkvm_curves::{traits::AffineCurve, PairingEngine};
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    bits::ToBytesGadget,
    fields::FpGadget,
    integers::uint::UInt8,
    traits::{
        alloc::AllocGadget,
        curves::{GroupGadget, PairingGadget},
        fields::ToConstraintFieldGadget,
    },
    Boolean,
    PrepareGadget,
    ToMinimalBitsGadget,
};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use crate::{
    sonic_pc::{Commitment, PreparedCommitmentVar},
    Vec,
};

/// Var for an optionally hiding Sonic-KZG10 commitment.
pub struct CommitmentVar<
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
> {
    /// Commitment.
    pub comm: PG::G1Gadget,
}

impl<TargetCurve, BaseCurve, PG> Clone for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn clone(&self) -> Self {
        Self { comm: self.comm.clone() }
    }
}

impl<TargetCurve, BaseCurve, PG> ToMinimalBitsGadget<<BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn to_minimal_bits<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        self.comm.to_minimal_bits(cs.ns(|| "comm"))
    }
}

impl<TargetCurve, BaseCurve, PG> AllocGadget<Commitment<TargetCurve>, <BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn alloc_constant<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Commitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|commitment| {
            let comm = *commitment.borrow();
            let comm_gadget =
                PG::G1Gadget::alloc_constant(cs.ns(|| "alloc_constant_commitment"), || Ok(comm.0.into_projective()))?;

            Ok(Self { comm: comm_gadget })
        })
    }

    fn alloc<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Commitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|commitment| {
            let comm = *commitment.borrow();
            let comm_gadget = PG::G1Gadget::alloc(cs.ns(|| "alloc_commitment"), || Ok(comm.0.into_projective()))?;

            Ok(Self { comm: comm_gadget })
        })
    }

    fn alloc_input<
        Fn: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Commitment<TargetCurve>>,
        CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>,
    >(
        mut cs: CS,
        value_gen: Fn,
    ) -> Result<Self, SynthesisError> {
        value_gen().and_then(|commitment| {
            let comm = *commitment.borrow();
            let comm_gadget =
                PG::G1Gadget::alloc_input(cs.ns(|| "alloc_input_commitment"), || Ok(comm.0.into_projective()))?;

            Ok(Self { comm: comm_gadget })
        })
    }
}

impl<TargetCurve, BaseCurve, PG> ToConstraintFieldGadget<<BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn to_constraint_field<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<FpGadget<<BaseCurve as PairingEngine>::Fr>>, SynthesisError> {
        self.comm.to_constraint_field(cs.ns(|| "comm_to_constraint_field"))
    }
}

impl<TargetCurve, BaseCurve, PG>
    PrepareGadget<PreparedCommitmentVar<TargetCurve, BaseCurve, PG>, <BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn prepare<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<PreparedCommitmentVar<TargetCurve, BaseCurve, PG>, SynthesisError> {
        let mut prepared_comm = Vec::<PG::G1Gadget>::new();
        let supported_bits = <<TargetCurve as PairingEngine>::Fr as PrimeField>::size_in_bits();

        let mut cur: PG::G1Gadget = self.comm.clone();
        for i in 0..supported_bits {
            prepared_comm.push(cur.clone());
            cur.double_in_place(cs.ns(|| format!("cur_double_in_place_{}", i)))?;
        }

        Ok(PreparedCommitmentVar::<TargetCurve, BaseCurve, PG> { prepared_comm })
    }
}

impl<TargetCurve, BaseCurve, PG> ToBytesGadget<<BaseCurve as PairingEngine>::Fr>
    for CommitmentVar<TargetCurve, BaseCurve, PG>
where
    TargetCurve: PairingEngine,
    BaseCurve: PairingEngine,
    PG: PairingGadget<TargetCurve, <BaseCurve as PairingEngine>::Fr>,
{
    fn to_bytes<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        mut cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.comm.to_bytes(cs.ns(|| "comm_to_bytes"))
    }

    fn to_bytes_strict<CS: ConstraintSystem<<BaseCurve as PairingEngine>::Fr>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}
