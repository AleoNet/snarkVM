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

use crate::testnet1::{parameters::SystemParameters, Testnet1Components};
use snarkvm_algorithms::traits::{CommitmentScheme, CRH};
use snarkvm_gadgets::{
    integers::uint::UInt8,
    traits::{
        algorithms::{CRHGadget, CommitmentGadget},
        alloc::AllocGadget,
    },
};
use snarkvm_r1cs::{errors::SynthesisError, Assignment, ConstraintSynthesizer, ConstraintSystem};

/// Always-accept program
pub struct NoopCircuit<C: Testnet1Components> {
    /// System parameters
    pub system_parameters: Option<SystemParameters<C>>,
    /// Commitment to the program input.
    pub local_data_root: Option<<C::LocalDataCRH as CRH>::Output>,
    /// Record position
    pub position: u8,
}

impl<C: Testnet1Components> NoopCircuit<C> {
    pub fn blank(system_parameters: &SystemParameters<C>) -> Self {
        Self {
            system_parameters: Some(system_parameters.clone()),
            local_data_root: Some(<C::LocalDataCRH as CRH>::Output::default()),
            position: 0u8,
        }
    }

    pub fn new(
        system_parameters: &SystemParameters<C>,
        local_data_root: &<C::LocalDataCRH as CRH>::Output,
        position: u8,
    ) -> Self {
        Self {
            system_parameters: Some(system_parameters.clone()),
            local_data_root: Some(local_data_root.clone()),
            position,
        }
    }
}

impl<C: Testnet1Components> ConstraintSynthesizer<C::InnerScalarField> for NoopCircuit<C> {
    fn generate_constraints<CS: ConstraintSystem<C::InnerScalarField>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let system_parameters = self.system_parameters.get_ref()?;
        let local_data_root = self.local_data_root.get_ref()?;
        let position = self.position;

        let _position = UInt8::alloc_input_vec_le(cs.ns(|| "Alloc position"), &[position])?;

        let _local_data_commitment_parameters_gadget =
            <C::LocalDataCommitmentGadget as CommitmentGadget<_, _>>::ParametersGadget::alloc_input(
                &mut cs.ns(|| "Declare local data commitment parameters"),
                || Ok(system_parameters.local_data_commitment.parameters().clone()),
            )?;

        let _local_data_root_gadget = <C::LocalDataCRHGadget as CRHGadget<_, _>>::OutputGadget::alloc_input(
            cs.ns(|| "Allocate local data root"),
            || Ok(local_data_root),
        )?;

        Ok(())
    }
}
