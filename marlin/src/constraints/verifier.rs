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

use crate::PolynomialCommitment;

use snarkvm_fields::PrimeField;
use snarkvm_gadgets::traits::fields::ToConstraintFieldGadget;
use snarkvm_polycommit::PCCheckVar;

use std::marker::PhantomData;

/// The Marlin verification gadget.
pub struct MarlinVerificationGadget<
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
>(
    PhantomData<TargetField>,
    PhantomData<BaseField>,
    PhantomData<PC>,
    PhantomData<PCG>,
);

impl<TargetField, BaseField, PC, PCG> MarlinVerificationGadget<TargetField, BaseField, PC, PCG>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    PC: PolynomialCommitment<TargetField>,
    PCG: PCCheckVar<TargetField, PC, BaseField>,
    PCG::VerifierKeyVar: ToConstraintFieldGadget<BaseField>,
    PCG::CommitmentVar: ToConstraintFieldGadget<BaseField>,
{
    /// The encoding of the protocol name for use as seed.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";
}
