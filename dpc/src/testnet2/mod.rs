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

pub mod dpc;
pub use dpc::*;

pub mod outer_circuit;
pub use outer_circuit::*;

pub mod universal_parameters;
pub use universal_parameters::*;

pub mod program;
pub use program::*;

pub mod parameters;

use crate::{Parameters, ProgramLocalData};
use snarkvm_algorithms::prelude::*;
use snarkvm_fields::ToConstraintField;
use snarkvm_gadgets::{bits::Boolean, nonnative::NonNativeFieldVar, traits::algorithms::SNARKVerifierGadget};
use snarkvm_marlin::{
    marlin::{MarlinMode, UniversalSRS},
    FiatShamirRng,
};
use snarkvm_polycommit::PolynomialCommitment;

/// Trait that stores information about the testnet2 DPC scheme.
pub trait Testnet2Components: Parameters {
    /// SNARK Verifier gadget for the inner circuit.
    type InnerSNARKGadget: SNARKVerifierGadget<Self::InnerSNARK, Input = Vec<Boolean>>;

    /// Program SNARK for Aleo applications.
    type ProgramSNARK: SNARK<
        ScalarField = Self::InnerScalarField,
        BaseField = Self::OuterScalarField,
        UniversalSetupParameters = UniversalSRS<Self::InnerScalarField, Self::PolynomialCommitment>,
        VerifierInput = ProgramLocalData<Self>,
    >;

    // TODO (raychu86): Look into properly declaring a proper input. i.e. Self::MarlinInputGadget.
    /// Program SNARK verifier gadget for Aleo applications.
    type ProgramSNARKGadget: SNARKVerifierGadget<
        Self::ProgramSNARK,
        Input = NonNativeFieldVar<Self::InnerScalarField, Self::OuterScalarField>,
    >;

    /// Polynomial commitment scheme for Program SNARKS using Marlin.
    type PolynomialCommitment: PolynomialCommitment<
        Self::InnerScalarField,
        VerifierKey = Self::PolynomialCommitmentVerifierKey,
        Commitment = Self::PolynomialCommitmentCommitment,
    >;
    type PolynomialCommitmentVerifierKey: ToConstraintField<Self::OuterScalarField>;
    type PolynomialCommitmentCommitment: ToConstraintField<Self::OuterScalarField>;

    /// Fiat Shamir RNG scheme used for Marlin SNARKS.
    type FiatShamirRng: FiatShamirRng<Self::InnerScalarField, Self::OuterScalarField>;

    /// Specify the Marlin mode (recursive or non-recursive) for program SNARKS.
    type MarlinMode: MarlinMode;
}
