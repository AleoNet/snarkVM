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

use crate::prelude::*;
use snarkvm_gadgets::integers::Sub;
use snarkvm_gadgets::prelude::*;

use anyhow::Result;
use std::marker::PhantomData;

pub trait Circuit<N: Network>: Send + Sync {
    // /// Returns the circuit ID.
    // fn circuit_id(&self) -> N::ProgramCircuitID;

    /// Returns the circuit type.
    fn circuit_type(&self) -> CircuitType;

    /// Returns the native evaluation of the circuit with the given inputs.
    fn evaluate<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
        inputs: &Vec<Record<N>>,
        // variables: &dyn PrivateVariables<N>,
    ) -> Result<Vec<Output<N>>>;

    // /// Executes the circuit, returning an proof.
    // fn execute(&self, record_position: u8, local_data: &LocalData<N>) -> Result<Execution<N>, ProgramError>;

    // /// Returns true if the execution of the circuit is valid.
    // fn verify(&self, record_position: u8, local_data: &LocalData<N>, proof: &<N::ProgramSNARK as SNARK>::Proof)
    //     -> bool;
}

// use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};
use snarkvm_r1cs::ConstraintSystem;

pub trait Logic<N: Network>: Send + Sync {
    /// Returns the circuit type.
    fn circuit_type(&self) -> CircuitType;

    // /// Synthesizes the circuit inside the given constraint system.
    // fn synthesize<CS: ConstraintSystem<N::InnerScalarField>>(
    //     &self,
    //     cs: &mut CS,
    //     public: &PublicVariables<N>,
    // ) -> Result<(), SynthesisError>;
}

#[derive(Clone)]
pub struct Output<N: Network> {
    address: Address<N>,
    value: AleoAmount,
    payload: Payload,
}

pub struct Transition<N: Network>(PhantomData<N>);

impl<N: Network> Transition<N> {
    fn add<L: FnOnce(&dyn PrivateVariables<N>) -> Result<Output<N>>>(
        logic: L,
        variables: &dyn PrivateVariables<N>,
    ) -> Result<Output<N>> {
        logic(variables)
    }

    fn split<
        CS: ConstraintSystem<N::InnerScalarField>,
        L: FnOnce(&mut CS, Record<N>, &dyn PrivateVariables<N>) -> Result<[Output<N>; 2]>,
    >(
        cs: &mut CS,
        logic: L,
        input: Record<N>,
        variables: &dyn PrivateVariables<N>,
    ) -> Result<[Output<N>; 2]> {
        logic(cs, input, variables)
    }
}

// pub struct TokenTransferVariables<N: Network> {
//     sender: Address<N>,
//     receiver: Address<N>,
//     amount: u64,
// }

pub struct TokenTransfer<N: Network> {
    sender: Address<N>,
    receiver: Address<N>,
    amount: u64,
}

impl<N: Network> Circuit<N> for TokenTransfer<N> {
    /// Returns the circuit type.
    fn circuit_type(&self) -> CircuitType {
        CircuitType::Split
    }

    /// Returns the native evaluation of the circuit with the given inputs.
    fn evaluate<CS: ConstraintSystem<N::InnerScalarField>>(
        &self,
        cs: &mut CS,
        inputs: &Vec<Record<N>>,
    ) -> Result<Vec<Output<N>>> {
        let logic = |cs: &mut CS, input: Record<N>, variables: &dyn PrivateVariables<N>| -> Result<[Output<N>; 2]> {
            let private = variables.as_any().downcast_ref::<TokenTransfer<N>>().unwrap();

            // let outputs = {
            //     assert_eq!(input.owner(), private.sender);
            //
            //     let sender_amount = *input.payload().as_any().downcast_ref::<u64>().unwrap();
            //     assert!(sender_amount >= private.amount);
            //
            //     let sender_change = sender_amount - private.amount;
            //
            //     [
            //         Output {
            //             address: private.sender.clone(),
            //             value: AleoAmount(0),
            //             payload: Payload::from(&sender_change.to_le_bytes()),
            //         },
            //         Output {
            //             address: private.receiver.clone(),
            //             value: AleoAmount(0),
            //             payload: Payload::from(&private.amount.to_le_bytes()),
            //         },
            //     ]
            // };

            // Enforce the sender matches.
            let sender = {
                let input_owner = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::PublicKeyGadget::alloc(
                    &mut cs.ns(|| "input_record_owner"),
                    || Ok(input.owner().encryption_key()),
                )?;

                let sender = <N::AccountEncryptionGadget as EncryptionGadget<
                    N::AccountEncryptionScheme,
                    N::InnerScalarField,
                >>::PublicKeyGadget::alloc(&mut cs.ns(|| "sender"), || {
                    Ok(private.sender.encryption_key())
                })?;

                input_owner.enforce_equal(&mut cs.ns(|| "enforce sender"), &sender)?;

                sender
            };

            // Enforce the amount is sufficient.
            let (sender_change, private_amount) = {
                let input_amount = *input.payload().as_any().downcast_ref::<u64>().unwrap();

                let input_amount_gadget = UInt64::alloc(&mut cs.ns(|| "input_amount"), || Ok(input_amount))?;

                let private_amount_gadget = UInt64::alloc(&mut cs.ns(|| "private_amount"), || Ok(private.amount))?;

                let is_geq = input_amount_gadget
                    .greater_than_or_equal(&mut cs.ns(|| "enforce amount"), &private_amount_gadget)?;

                is_geq.enforce_equal(&mut cs.ns(|| "enforce geq"), &Boolean::Constant(true))?;

                let sender_change_gadget =
                    input_amount_gadget.sub(&mut cs.ns(|| "subtract amount"), &private_amount_gadget)?;

                (sender_change_gadget, private_amount_gadget)
            };

            // Alloc the receiver.
            let receiver = <N::AccountEncryptionGadget as EncryptionGadget<
                N::AccountEncryptionScheme,
                N::InnerScalarField,
            >>::PublicKeyGadget::alloc(&mut cs.ns(|| "receiver"), || {
                Ok(private.receiver.encryption_key())
            })?;

            let outputs = [
                Output::new(sender, 0, sender_change),
                Output::new(receiver, 0, private_amount),
            ];

            Ok(outputs)
        };

        assert_eq!(inputs.len(), self.circuit_type().input_count() as usize);
        let outputs = Transition::split(cs, logic, inputs[0].clone(), self)?;
        assert_eq!(outputs.len(), self.circuit_type().output_count() as usize);

        Ok(outputs.to_vec())
    }
}

impl<N: Network> PrivateVariables<N> for TokenTransfer<N> {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}
