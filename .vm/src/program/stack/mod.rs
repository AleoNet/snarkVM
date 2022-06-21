// Copyright (C) 2019-2022 Aleo Systems Inc.
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

mod circuit_value;
pub(crate) use circuit_value::*;

mod stack_value;
pub use stack_value::*;

mod load;
mod store;

use crate::{Operand, Program, RegisterTypes};
use console::{
    network::prelude::*,
    program::{Ciphertext, Entry, Identifier, Literal, Plaintext, Record, Register, Value, ValueType},
    types::{Address, Field, Group, Scalar, U16},
};

use indexmap::IndexMap;

use console::network::BHPMerkleTree;
use core::marker::PhantomData;

pub enum TraceValue<N: Network> {
    /// A plaintext value.
    Plaintext(Plaintext<N>),
    /// A record value, and the leaf value.
    Record(Record<N, Plaintext<N>>, Record<N, Ciphertext<N>>),
}

/// N::TRACE_DEPTH
const TRANSACTION_DEPTH: u8 = 4;
/// N::TRACE_DEPTH
const TRANSITION_DEPTH: u8 = 4;

/// The trace is a two-tier Merkle tree system that tracks the inputs and outputs for all transitions in a transaction.
/// ```ignore
///                                          transaction_root
///                                               /
///                                            ...
///                                            /
///                                    transition_root_0
///                              /                            \
///                         node_0                             node_1
///                    /           \                      /               \
///                       ...                                      ...
///              /                   \                 /                     \
///         node_0       ...       node_3            node_4        ...       node_7
///       /       \              /       \         /        \              /       \
/// \[input_0, input_1, ..., input_6, input_7, output_0, output_1, ..., output_6, output_7\]
/// ```
pub struct Trace<N: Network, A: circuit::Aleo<Network = N>> {
    /// The Merkle tree of transition roots.
    transaction: BHPMerkleTree<N, TRANSACTION_DEPTH>,
    /// The root for the `i-th` transition.
    roots: IndexMap<u8, Field<N>>,
    /// The leaves for the `i-th` transition.
    leaves: IndexMap<u8, Vec<Option<Field<N>>>>,
    /// The caller of the current transition.
    caller: Address<N>,
    /// The current transition view key commitment randomizer.
    r_tcm: Field<N>,
    /// The current transition view key commitment (i.e. `tcm := Hash(caller, tpk, tvk)`).
    tcm: Field<N>,
    /// The current transition public key (i.e. `tpk := Hash(r_tcm) * G`).
    tpk: Group<N>,
    /// The current transition view key (i.e. `tvk := tsk * caller`).
    tvk: Group<N>,
    /// The tracker for the current transition index.
    transition_index: u8,
    /// The tracker for the current input index.
    input_index: u8,
    /// The tracker for the current output index.
    output_index: u8,
    /// The boolean indicator if the trace is finalized.
    is_finalized: bool,
    /// PhantomData.
    _phantom: PhantomData<A>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Trace<N, A> {
    /// Initializes a new stack trace.
    pub fn new<R: Rng + CryptoRng>(caller: Address<N>, rng: &mut R) -> Result<Self> {
        // Compute the transition view key.
        let (r_tcm, tcm, tpk, tvk) = Self::compute_tvk::<R>(caller, rng)?;

        Ok(Self {
            transaction: N::merkle_tree_bhp::<TRANSACTION_DEPTH>(&[])?,
            roots: IndexMap::new(),
            leaves: IndexMap::new(),
            caller,
            r_tcm,
            tcm,
            tpk,
            tvk,
            transition_index: 0,
            input_index: 0,
            output_index: 0,
            is_finalized: false,
            _phantom: PhantomData,
        })
    }

    /// Returns the roots.
    pub const fn roots(&self) -> &IndexMap<u8, Field<N>> {
        &self.roots
    }

    /// Returns the leaves.
    pub const fn leaves(&self) -> &IndexMap<u8, Vec<Option<Field<N>>>> {
        &self.leaves
    }

    /// Returns the current caller.
    pub const fn caller(&self) -> &Address<N> {
        &self.caller
    }

    /// Returns the current transition view key commitment randomizer.
    pub const fn r_tcm(&self) -> &Field<N> {
        &self.r_tcm
    }

    /// Returns the current transition view key commitment.
    pub const fn tcm(&self) -> &Field<N> {
        &self.tcm
    }

    /// Returns the current transition public key.
    pub const fn tpk(&self) -> &Group<N> {
        &self.tpk
    }

    /// Returns the current transition view key.
    pub const fn tvk(&self) -> &Group<N> {
        &self.tvk
    }

    /// Adds an input to the trace.
    pub fn add_input(&mut self, input: Field<N>) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is finalized, cannot add input");
        // Ensure the input index is within the bounds of the program.
        ensure!((self.input_index as usize) < N::MAX_INPUTS, "Trace reached the maximum inputs for a program call");
        // Ensure the input is nonzero.
        ensure!(!input.is_zero(), "Input to the trace must be nonzero");

        // Add the input to the trace.
        self.leaves.entry(self.transition_index).or_default().push(Some(input));
        // Increment the input index.
        self.input_index += 1;

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()
    }

    /// Adds an output to the trace.
    pub fn add_output(&mut self, output: Field<N>) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is finalized, cannot add output");
        // Ensure the output index is within the bounds of the program.
        ensure!((self.output_index as usize) < N::MAX_OUTPUTS, "Trace reached the maximum outputs for a program call");
        // Ensure the output is nonzero.
        ensure!(!output.is_zero(), "Output to the trace must be nonzero");

        // If this is the first call to output, fast forward the input index to the end of the inputs.
        if self.output_index == 0 {
            // Pad the leaves up to the starting index for the outputs.
            self.leaves
                .entry(self.transition_index)
                .or_default()
                .extend(vec![None; N::MAX_INPUTS - self.input_index as usize]);
            // Set the input index to the end of the inputs.
            self.input_index = N::MAX_INPUTS as u8;
        }

        // Add the output to the trace.
        self.leaves.entry(self.transition_index).or_default().push(Some(output));
        // Increment the output index.
        self.output_index += 1;

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()
    }

    /// Updates the current caller, transition view key, transition index, input index, and output index.
    pub fn next_transition<R: Rng + CryptoRng>(&mut self, caller: Address<N>, rng: &mut R) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is finalized, cannot call next transition");
        // Ensure the number of transition roots is correct.
        ensure!(self.roots.len() == self.transition_index as usize, "Trace has incorrect number of transition roots");
        // Ensure the transition index is within the bounds of the trace.
        ensure!((self.transition_index as usize) < N::MAX_TRANSITIONS, "Trace reached the maximum transitions");
        // Ensure the input index or output index is nonzero.
        ensure!(self.input_index > 0 || self.output_index > 0, "Trace cannot transition without inputs or outputs");

        // Pad the leaves up to the starting index of the next transition.
        self.leaves
            .entry(self.transition_index)
            .or_default()
            .extend(vec![None; N::MAX_INPUTS - self.input_index as usize]);
        self.leaves
            .entry(self.transition_index)
            .or_default()
            .extend(vec![None; N::MAX_OUTPUTS - self.output_index as usize]);

        // Compute the transition tree.
        let transition = N::merkle_tree_bhp::<TRANSITION_DEPTH>(
            &self
                .leaves
                .get(&self.transition_index)
                .unwrap_or(&vec![])
                .iter()
                .map(|leaf| leaf.unwrap_or(Field::<N>::zero()).to_bits_le())
                .collect::<Vec<_>>(),
        )?;
        // Add the transition root to the Merkle tree.
        self.transaction.append(&[transition.root().to_bits_le()])?;
        self.roots.insert(self.transition_index, *transition.root());

        // Update the caller.
        self.caller = caller;

        // Update the transition view key.
        let (r_tcm, tcm, tpk, tvk) = Self::compute_tvk::<R>(caller, rng)?;
        self.r_tcm = r_tcm;
        self.tcm = tcm;
        self.tpk = tpk;
        self.tvk = tvk;

        // Increment the transition index.
        self.transition_index += 1;
        // Reset the input and output indices.
        self.input_index = 0;
        self.output_index = 0;

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()
    }

    /// Finalizes the trace.
    pub fn finalize(&mut self) -> Result<()> {
        // Ensure the trace is not finalized.
        ensure!(!self.is_finalized, "Trace is already finalized");
        // Ensure the number of transition roots is correct.
        ensure!(self.roots.len() == self.transition_index as usize, "Trace has incorrect number of transition roots");
        // Ensure the transition index is within the bounds of the trace.
        ensure!((self.transition_index as usize) < N::MAX_TRANSITIONS, "Trace reached the maximum transitions");

        // If the input index or output index is nonzero, finalize the current transition.
        if self.input_index > 0 || self.output_index > 0 {
            // Pad the leaves up to the starting index of the next transition.
            self.leaves
                .entry(self.transition_index)
                .or_default()
                .extend(vec![None; N::MAX_INPUTS - self.input_index as usize]);
            self.leaves.entry(self.transition_index).or_default().extend(vec![
                None;
                N::MAX_OUTPUTS
                    - self.output_index as usize
            ]);

            // Compute the transition tree.
            let transition = N::merkle_tree_bhp::<TRANSITION_DEPTH>(
                &self
                    .leaves
                    .get(&self.transition_index)
                    .unwrap_or(&vec![])
                    .iter()
                    .map(|leaf| leaf.unwrap_or(Field::<N>::zero()).to_bits_le())
                    .collect::<Vec<_>>(),
            )?;
            // Add the transition root to the Merkle tree.
            self.transaction.append(&[transition.root().to_bits_le()])?;
            self.roots.insert(self.transition_index, *transition.root());

            // Increment the transition index.
            self.transition_index += 1;
            // Reset the input and output indices.
            self.input_index = 0;
            self.output_index = 0;
        }

        // Ensure the number of leaves is correct.
        self.ensure_num_leaves()
    }

    /// Ensures the current number of leaves is correct.
    pub fn ensure_num_leaves(&self) -> Result<()> {
        // Compute the number of leaves.
        let num_leaves = self.leaves.values().fold(0, |acc, v| acc + v.len());
        // Compute the expected number of leaves.
        let expected_num_leaves = self.transition_index as usize * (N::MAX_INPUTS + N::MAX_OUTPUTS) as usize
            + (self.input_index + self.output_index) as usize;
        // Ensure the number of leaves is correct.
        ensure!(
            num_leaves == expected_num_leaves,
            "Trace has an incorrect number of leaves: expected {expected_num_leaves}, found {num_leaves}"
        );
        Ok(())
    }

    /// Returns the transition view key, given the caller address and an RNG.
    pub(crate) fn compute_tvk<R: Rng + CryptoRng>(
        caller: Address<N>,
        rng: &mut R,
    ) -> Result<(Field<N>, Field<N>, Group<N>, Group<N>)> {
        // Sample a random nonce.
        let r_tcm = Uniform::rand(rng);
        // Compute the transition secret key `tsk` as `HashToScalar(r_tcm)`.
        // TODO (howardwu): Domain separator.
        // let tsk = N::hash_to_scalar_psd2(&[N::tvk_domain(), r_tcm])?;
        let tsk = N::hash_to_scalar_psd2(&[r_tcm])?;
        // Compute the transition public key `tpk` as `tsk * G`.
        let tpk = N::g_scalar_multiply(&tsk);
        // Compute the transition view key `tvk` as `tsk * caller`.
        let tvk = *caller * tsk;
        // Compute the transition view key commitment `tcm` := `Hash(tvk)`.
        // TODO (howardwu): Domain separator.
        // Compute the transition view key commitment `tcm` as `Hash(caller, tpk, tvk)`.
        let tcm = N::hash_psd4(&[*caller, tpk, tvk].map(|c| c.to_x_coordinate()))?;
        Ok((r_tcm, tcm, tpk, tvk))
    }

    // /// Returns the encryption randomizer for the given input index.
    // pub(crate) fn compute_input_randomizer(&self, input_index: u16) -> Result<Field<N>> {
    //     // Compute the encryption randomizer as `Hash(tvk || index)`.
    //     N::hash_psd2(&[self.tvk.to_x_coordinate(), U16::new(input_index).to_field()?])
    // }

    // /// Returns the encryption randomizer for the given output index.
    // pub(crate) fn compute_output_randomizer(&self, index: u16) -> Result<Field<N>> {
    //     // Compute the index.
    //     let index = U16::new(N::MAX_OUTPUTS as u16 + index).to_field()?;
    //     // Compute the encryption randomizer as `Hash(tvk || index)`.
    //     N::hash_psd2(&[self.tvk.to_x_coordinate(), index])
    // }
}

pub struct Stack<N: Network, A: circuit::Aleo<Network = N>> {
    /// The program (record types, interfaces, functions).
    program: Program<N, A>,
    /// The mapping of all registers to their defined types.
    register_types: RegisterTypes<N>,
    /// The mapping of assigned console registers to their values.
    console_registers: IndexMap<u64, StackValue<N>>,
    /// The mapping of assigned circuit registers to their values.
    circuit_registers: IndexMap<u64, CircuitValue<A>>,
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Executes a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute_transition(
        trace: &mut Trace<N, A>,
        program: Program<N, A>,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<circuit::Value<A, circuit::Plaintext<A>>>> {
        // Ensure the circuit environment is clean.
        A::reset();

        // Retrieve the function from the program.
        let function = program.get_function(function_name)?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Retrieve the register types for the function.
        let register_types = program.get_function_registers(function_name)?;
        // Initialize the stack.
        let mut stack = Self::new(program, register_types)?;

        // Store the inputs.
        function.inputs().iter().zip_eq(inputs).try_for_each(|(input_type, input)| {
            // Retrieve the register and value type.
            let (register, value_type) = (input_type.register(), input_type.value_type());

            // Assign the console input to the register.
            stack.store(&register, input.clone())?;
            // Compute the console input leaf.
            let console_input_leaf = N::hash_bhp1024(&input.to_bits_le())?;
            // Add the console input leaf to the trace.
            trace.add_input(console_input_leaf)?;

            use circuit::{Inject, ToBits};

            // Inject the console input into a circuit input.
            let circuit_input = match value_type {
                // Constant inputs are injected as constants.
                ValueType::Constant(..) => CircuitValue::new(circuit::Mode::Constant, input.clone()),
                // Public and private inputs are injected as privates.
                // Records are injected based on inherited visibility (the Mode::Private is overridden).
                ValueType::Public(..) | ValueType::Private(..) | ValueType::Record(..) => {
                    CircuitValue::new(circuit::Mode::Private, input.clone())
                }
            };
            // Assign the circuit input to the register.
            stack.store_circuit(&register, circuit_input.clone())?;

            // Compute the circuit input leaf.
            let circuit_input_leaf = A::hash_bhp1024(&circuit_input.to_bits_le());
            // Ensure the console input leaf matches the computed input leaf.
            A::assert_eq(&circuit_input_leaf, circuit::Field::<A>::new(circuit::Mode::Public, console_input_leaf));

            Ok::<_, Error>(())
        })?;

        // Execute the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.evaluate(&mut stack))?;
        function.instructions().iter().try_for_each(|instruction| instruction.execute(&mut stack))?;

        // Load the outputs.
        let outputs = function.outputs().iter().enumerate().map(|(index, output)| {
            use circuit::{Eject, Inject, ToBits};

            // Retrieve the circuit output from the register.
            let circuit_output = stack.load_circuit(&Operand::Register(output.register().clone()))?;
            // Compute the circuit output leaf.
            let circuit_output_leaf = A::hash_bhp1024(&circuit_output.to_bits_le());

            // Eject to the console output leaf.
            let console_output_leaf = circuit_output_leaf.eject_value();
            // Add the console output leaf to the trace.
            trace.add_output(console_output_leaf)?;

            // Ensure the console output leaf matches the computed output leaf.
            A::assert_eq(&circuit_output_leaf, circuit::Field::<A>::new(circuit::Mode::Public, console_output_leaf));

            // Construct the circuit output value.
            let output = match (circuit_output, output.value_type()) {
                (CircuitValue::Plaintext(plaintext), ValueType::Constant(..)) => circuit::Value::Constant(plaintext),
                (CircuitValue::Plaintext(plaintext), ValueType::Public(..)) => circuit::Value::Public(plaintext),
                (CircuitValue::Plaintext(plaintext), ValueType::Private(..)) => circuit::Value::Private(plaintext),
                (CircuitValue::Record(record), ValueType::Record(..)) => circuit::Value::Record(record),
                _ => bail!("Circuit value does not match the expected output type"),
            };
            // Return the output.
            Ok(output)
        });

        outputs.collect()
    }
}

impl<N: Network, A: circuit::Aleo<Network = N>> Stack<N, A> {
    /// Initializes a new stack, given the program and register types.
    #[inline]
    pub fn new(program: Program<N, A>, register_types: RegisterTypes<N>) -> Result<Self> {
        Ok(Self { program, register_types, console_registers: IndexMap::new(), circuit_registers: IndexMap::new() })
    }

    /// Returns the program.
    #[inline]
    pub const fn program(&self) -> &Program<N, A> {
        &self.program
    }

    /// Evaluates a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn evaluate(
        program: Program<N, A>,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<Value<N, Plaintext<N>>>> {
        // Retrieve the function from the program.
        let function = program.get_function(function_name)?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Retrieve the register types.
        let register_types = program.get_function_registers(function_name)?;
        // Initialize the stack.
        let mut stack = Self::new(program, register_types.clone())?;

        // Store the inputs.
        function.inputs().iter().map(|i| i.register()).zip_eq(inputs).try_for_each(|(register, input)| {
            // Assign the input value to the register.
            stack.store(&register, input.clone())
        })?;

        // Evaluate the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.evaluate(&mut stack))?;

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the stack value from the register.
            let stack_value = stack.load(&Operand::Register(output.register().clone()))?;
            // Convert the stack value to the output value type.
            let output = match (stack_value, output.value_type()) {
                (StackValue::Plaintext(plaintext), ValueType::Constant(..)) => Value::Constant(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Public(..)) => Value::Public(plaintext),
                (StackValue::Plaintext(plaintext), ValueType::Private(..)) => Value::Private(plaintext),
                (StackValue::Record(record), ValueType::Record(..)) => Value::Record(record),
                _ => bail!("Stack value does not match the expected output type"),
            };
            // Return the output.
            Ok(output)
        });

        outputs.collect()
    }

    /// Executes a program function on the given inputs.
    ///
    /// # Errors
    /// This method will halt if the given inputs are not the same length as the input statements.
    #[inline]
    pub fn execute(
        program: Program<N, A>,
        function_name: &Identifier<N>,
        inputs: &[StackValue<N>],
    ) -> Result<Vec<circuit::Value<A, circuit::Plaintext<A>>>> {
        // Retrieve the function from the program.
        let function = program.get_function(function_name)?;
        // Ensure the number of inputs matches the number of input statements.
        if function.inputs().len() != inputs.len() {
            bail!("Expected {} inputs, found {}", function.inputs().len(), inputs.len())
        }

        // Retrieve the register types for the function.
        let register_types = program.get_function_registers(function_name)?;
        // Initialize the stack.
        let mut stack = Self::new(program, register_types)?;

        // Store the inputs.
        function.inputs().iter().map(|i| (i.register(), i.value_type())).zip_eq(inputs).try_for_each(
            |((register, value_type), input)| {
                // Assign the console input to the register.
                stack.store(&register, input.clone())?;
                // Assign the circuit input to the register.
                stack.store_circuit(&register, match value_type {
                    ValueType::Constant(..) => circuit::Inject::new(circuit::Mode::Constant, input.clone()),
                    ValueType::Public(..) => circuit::Inject::new(circuit::Mode::Public, input.clone()),
                    ValueType::Private(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                    ValueType::Record(..) => circuit::Inject::new(circuit::Mode::Private, input.clone()),
                })
            },
        )?;

        // Execute the instructions.
        function.instructions().iter().try_for_each(|instruction| instruction.evaluate(&mut stack))?;
        function.instructions().iter().try_for_each(|instruction| instruction.execute(&mut stack))?;

        // Load the outputs.
        let outputs = function.outputs().iter().map(|output| {
            // Retrieve the circuit output from the register.
            let circuit_output = stack.load_circuit(&Operand::Register(output.register().clone()))?;
            // Construct the circuit output value.
            let output = match (circuit_output, output.value_type()) {
                (CircuitValue::Plaintext(plaintext), ValueType::Constant(..)) => circuit::Value::Constant(plaintext),
                (CircuitValue::Plaintext(plaintext), ValueType::Public(..)) => circuit::Value::Public(plaintext),
                (CircuitValue::Plaintext(plaintext), ValueType::Private(..)) => circuit::Value::Private(plaintext),
                (CircuitValue::Record(record), ValueType::Record(..)) => circuit::Value::Record(record),
                _ => bail!("Circuit value does not match the expected output type"),
            };
            // Return the output.
            Ok(output)
        });

        outputs.collect()
    }
}
