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

use std::{borrow::Cow, marker::PhantomData};

use anyhow::*;
use indexmap::IndexMap;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{Boolean, CondSelectGadget};
use snarkvm_ir::{Input as IrInput, InputData, Instruction, Program, RepeatData, Type, Value};
use snarkvm_r1cs::ConstraintSystem;

use crate::{
    bool_from_input,
    errors::{GroupError, ValueError},
    Address, Char, ConstrainedValue, Evaluator, FieldType, GroupType, Integer,
};
use im::HashMap;

mod instruction;
mod state;

pub use instruction::*;
use state::*;

/// An evaluator for filling out a R1CS while also producing an expected output.
pub struct SetupEvaluator<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> {
    cs: CS,
    _p: PhantomData<(F, G)>,
}

impl<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> SetupEvaluator<F, G, CS> {
    pub fn new(cs: CS) -> Self {
        Self { cs, _p: PhantomData }
    }
}

impl<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> Evaluator<F, G> for SetupEvaluator<F, G, CS> {
    type Error = anyhow::Error;
    type Output = ConstrainedValue<F, G>;

    fn evaluate(&mut self, program: &Program, input: &InputData) -> Result<Self::Output, Self::Error> {
        let mut state = EvaluatorState::new(program);

        state.handle_input_block("main", &program.header.main_inputs, &input.main, &mut self.cs)?;
        state.handle_const_input_block(&program.header.constant_inputs, &input.constants, &mut self.cs)?;
        state.handle_input_block(
            "register",
            &program.header.register_inputs,
            &input.registers,
            &mut self.cs,
        )?;
        state.handle_input_block(
            "public_states",
            &program.header.public_states,
            &input.public_states,
            &mut self.cs,
        )?;
        state.handle_input_block(
            "private_record_states",
            &program.header.private_record_states,
            &input.private_record_states,
            &mut self.cs,
        )?;
        state.handle_input_block(
            "private_leaf_states",
            &program.header.private_leaf_states,
            &input.private_leaf_states,
            &mut self.cs,
        )?;

        let output = state.evaluate_function(0, &[], &mut self.cs)?; // arguments assigned via input system for entrypoint
        Ok(output)
    }
}
