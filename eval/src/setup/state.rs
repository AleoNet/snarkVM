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

use snarkvm_gadgets::{Integer as GadgetInteger, UInt16, UInt32, UInt8};
use snarkvm_ir::{CallData, Function, MaskData, RepeatData};

use crate::IntegerType;

use super::*;

use std::{convert::TryInto, fmt, mem, rc::Rc};

/// the possible outcomes of evaluating an instruction
#[derive(Debug)]
enum ControlFlow<'a> {
    Continue,
    Return,
    Recurse(&'a Instruction),
}

/// data concerning the parent instruction of a scope
#[derive(Debug)]
enum ParentInstruction<'a> {
    None,
    Call(&'a CallData),
    Mask(Boolean),
    Repeat(u32),
}

pub(super) struct FunctionEvaluator<'a, F: PrimeField, G: GroupType<F>> {
    call_stack: Vec<StateData<'a, F, G>>,
    state_data: StateData<'a, F, G>,
    namespace_id_counter: usize,
}

impl<'a, F: PrimeField, G: GroupType<F>> FunctionEvaluator<'a, F, G> {
    fn nest(&mut self, state: StateData<'a, F, G>) {
        self.call_stack.push(mem::replace(&mut self.state_data, state));
    }

    fn unnest(&mut self) -> StateData<'a, F, G> {
        let last_state = self.call_stack.pop().expect("no state to return to");
        mem::replace(&mut self.state_data, last_state)
    }

    // /// if run condition `false`, returns error; else returns to last state with `true` run condition
    // fn unwind(&mut self, e: Error) -> Result<()> {
    //     if self.state_data.condition {
    //         return Err(anyhow!(
    //             "f#{} i#{}: {:?}",
    //             self.state_data.function_index,
    //             self.state_data.state.instruction_index,
    //             e
    //         ));
    //     } else {
    //         self.call_stack = self.call_stack.drain(..).rev().skip_while(|s| !s.condition).collect();
    //         self.call_stack.reverse();
    //         self.state_data = self.call_stack.pop().expect("no state to return to");
    //         Ok(())
    //     }
    // }

    /// setup the state and call stack to start evaluating the target call instruction
    fn setup_call<CS: ConstraintSystem<F>>(&mut self, data: &'a CallData, cs: &mut CS) -> Result<()> {
        let arguments = data
            .arguments
            .iter()
            .map(|x| self.state_data.state.resolve(x, cs).map(|x| x.into_owned()))
            .collect::<Result<Vec<_>, _>>()?;

        self.namespace_id_counter += 1;
        let mut parent_variables = self.state_data.state.parent_variables.clone();
        parent_variables.extend(self.state_data.state.variables.clone());
        let mut state = EvaluatorState {
            program: self.state_data.state.program,
            variables: IndexMap::new(),
            call_depth: self.state_data.state.call_depth,
            parent_variables, // todo: eval perf of IndexMap here
            function_index: self.state_data.state.function_index,
            instruction_index: 0,
            namespace_id: self.namespace_id_counter,
        };
        state.cs_meta("function call", cs);

        let function = state.setup_evaluate_function(data.index, &arguments)?;
        let state_data = StateData {
            arguments: Rc::new(arguments),
            function: &function,
            function_index: data.index,
            block_start: 0,
            block_instruction_count: function.instructions.len() as u32,
            state,
            parent_instruction: ParentInstruction::Call(data),
            result: None,
            condition: self.state_data.condition,
        };

        self.state_data.state.instruction_index += 1;
        self.nest(state_data);
        if self.state_data.state.call_depth > self.state_data.state.program.header.inline_limit {
            Err(anyhow!("max inline limit hit"))
        } else if self.call_stack.iter().any(|old_state| {
            old_state.arguments == self.state_data.arguments
                && old_state.function_index == self.state_data.function_index
        }) {
            Err(anyhow!("infinite recursion detected"))
        } else {
            Ok(())
        }
    }

    /// returns to the previous state in the call stack and stores the result of the function call's evaluation
    fn finish_call(&mut self, data: &CallData) -> Result<()> {
        let res = self.unnest().result.unwrap_or_else(|| ConstrainedValue::Tuple(vec![]));
        self.state_data.state.store(data.destination, res);
        Ok(())
    }

    /// setup the state and call stack to start evaluating the target mask instruction
    fn setup_mask<CS: ConstraintSystem<F>>(&mut self, data: &'a MaskData, cs: &mut CS) -> Result<()> {
        if data.instruction_count + self.state_data.state.instruction_index
            >= self.state_data.function.instructions.len() as u32
        {
            return Err(anyhow!("illegal mask block length"));
        }

        let condition = self
            .state_data
            .state
            .resolve(&data.condition, cs)?
            .into_owned()
            .extract_bool()
            .map_err(|value| anyhow!("illegal condition type for conditional block: {}", value))?
            .clone();

        self.state_data.state.instruction_index += 1;

        let condition_const_value = match &condition {
            Boolean::Constant(c) => *c,
            _ => true,
        };

        if condition_const_value {
            self.namespace_id_counter += 1;

            let mut parent_variables = self.state_data.state.parent_variables.clone();
            parent_variables.extend(self.state_data.state.variables.clone());
            let state = EvaluatorState {
                program: self.state_data.state.program,
                variables: IndexMap::new(),
                call_depth: self.state_data.state.call_depth,
                parent_variables, // todo: eval perf of IndexMap here
                function_index: self.state_data.state.function_index,
                instruction_index: self.state_data.state.instruction_index,
                namespace_id: self.namespace_id_counter,
            };
            let state_data = StateData {
                arguments: self.state_data.arguments.clone(),
                function: self.state_data.function,
                function_index: self.state_data.function_index,
                block_start: self.state_data.state.instruction_index,
                block_instruction_count: data.instruction_count,
                state,
                parent_instruction: ParentInstruction::Mask(condition),
                result: self.state_data.result.clone(),
                condition: self.state_data.condition && condition.get_value().unwrap_or(true),
            };

            self.state_data.state.instruction_index += data.instruction_count;
            self.nest(state_data);
        } else {
            self.state_data.state.instruction_index += data.instruction_count;
        }
        Ok(())
    }

    /// returns to the previous state in the call stack and updates variables from the mask instructions evaluation
    fn finish_mask<CS: ConstraintSystem<F>>(&mut self, condition: Boolean, cs: &mut CS) -> Result<()> {
        let inner_state = self.unnest();
        let assignments = inner_state.state.variables;
        let target_index = inner_state.block_start + inner_state.block_instruction_count;
        let result = inner_state.result.clone();
        for (variable, value) in assignments {
            if let Some(prior) = self.state_data.state.variables.get(&variable).or(self
                .state_data
                .state
                .parent_variables
                .get(&variable))
            {
                let prior = prior.clone(); //todo: optimize away clone
                let value = ConstrainedValue::conditionally_select(
                    &mut self.state_data.state.cs_meta(&*format!("selection {}", variable), cs),
                    &condition,
                    &value,
                    &prior,
                )?;
                self.state_data.state.store(variable, value);
            }
        }
        assert_eq!(self.state_data.state.instruction_index, target_index);
        match (self.state_data.result.clone(), result.clone()) {
            (Some(prior), Some(interior)) => {
                self.state_data.result = Some(ConstrainedValue::conditionally_select(
                    &mut self.state_data.state.cs_meta(&*format!("selection result"), cs),
                    &condition,
                    &interior,
                    &prior,
                )?);
            }
            (None, Some(interior)) => {
                // will produce garbage if invalid IR (incomplete return path)
                self.state_data.result = Some(interior);
            }
            (_, None) => (),
        }
        Ok(())
    }

    /// setup the state and call stack to start evaluating the target repeat instruction.
    /// creates a state for every iteration and adds them all to the call stack
    fn setup_repeat<CS: ConstraintSystem<F>>(&mut self, data: &'a RepeatData, cs: &mut CS) -> Result<()> {
        if data.instruction_count + self.state_data.state.instruction_index
            >= self.state_data.function.instructions.len() as u32
        {
            return Err(anyhow!("illegal repeat block length"));
        }

        let from = self.state_data.state.resolve(&data.from, cs)?.into_owned();
        let from_int = from
            .extract_integer()
            .map_err(|value| anyhow!("illegal type for loop init: {}", value))?
            .to_owned();
        let from = from_int
            .to_usize()
            .ok_or_else(|| anyhow!("illegal input-derived loop index"))?;

        let to = self.state_data.state.resolve(&data.to, cs)?.into_owned();
        let to = to
            .extract_integer()
            .map_err(|value| anyhow!("illegal type for loop terminator: {}", value))?
            .to_usize()
            .ok_or_else(|| anyhow!("illegal input-derived loop terminator"))?;

        let iter: Box<dyn Iterator<Item = usize>> = match (from < to, data.inclusive) {
            (true, true) => Box::new(from..=to),
            (true, false) => Box::new(from..to),
            (false, true) => Box::new((to..=from).rev()),
            // add the range to the values to get correct bound
            (false, false) => Box::new(((to + 1)..(from + 1)).rev()),
        };

        self.state_data.state.instruction_index += 1;
        let mut iter_state_data = Vec::new();
        //todo: max loop count (DOS vector)
        for i in iter {
            self.namespace_id_counter += 1;
            let mut parent_variables = self.state_data.state.parent_variables.clone();
            parent_variables.extend(self.state_data.state.variables.clone());
            let mut state = EvaluatorState {
                program: self.state_data.state.program,
                variables: IndexMap::new(),
                call_depth: self.state_data.state.call_depth,
                parent_variables, // todo: eval perf of IndexMap here
                function_index: self.state_data.state.function_index,
                instruction_index: self.state_data.state.instruction_index,
                namespace_id: self.namespace_id_counter,
            };
            state.variables.insert(
                data.iter_variable,
                ConstrainedValue::Integer(match from_int.get_type() {
                    IntegerType::U8 => Integer::U8(UInt8::constant(
                        i.try_into().map_err(|_| anyhow!("loop index out of range for u8"))?,
                    )),
                    IntegerType::U16 => Integer::U16(UInt16::constant(
                        i.try_into().map_err(|_| anyhow!("loop index out of range for u16"))?,
                    )),
                    IntegerType::U32 => Integer::U32(UInt32::constant(
                        i.try_into().map_err(|_| anyhow!("loop index out of range for u32"))?,
                    )),
                    _ => return Err(anyhow!("illegal type for loop index")),
                }),
            );
            let new_state_data = StateData {
                arguments: self.state_data.arguments.clone(),
                function: self.state_data.function,
                function_index: self.state_data.function_index,
                block_start: self.state_data.state.instruction_index,
                block_instruction_count: data.instruction_count,
                state,
                parent_instruction: ParentInstruction::Repeat(data.iter_variable),
                result: self.state_data.result.clone(),
                condition: self.state_data.condition,
            };
            iter_state_data.push(new_state_data);
        }
        iter_state_data.reverse();
        self.state_data.state.instruction_index += data.instruction_count;
        if !iter_state_data.is_empty() {
            let new_state = iter_state_data.pop().unwrap();
            self.nest(new_state);
            self.call_stack.extend(iter_state_data.into_iter());
        }
        Ok(())
    }

    /// returns to the previous state in the call stack and updates variables from the repeat instructions evaluation
    fn finish_repeat(&mut self, iter_variable: u32) -> Result<()> {
        let inner_state = self.unnest();
        for (variable, value) in inner_state.state.variables {
            if self
                .state_data
                .state
                .variables
                .get(&variable)
                .or(self.state_data.state.parent_variables.get(&variable))
                .is_some()
                && variable != iter_variable
            {
                self.state_data.state.store(variable, value);
            }
        }
        Ok(())
    }

    /// returns the output of the initial function call's evaluation. panics if the call stack isn't empty
    fn finish_evaluation(self) -> ConstrainedValue<F, G> {
        if !self.call_stack.is_empty() {
            panic!(
                "cant finish evaluation if call stack's not_empty. {:?} element(s) remain",
                self.call_stack.len()
            )
        }
        let res = self
            .state_data
            .result
            .unwrap_or_else(|| ConstrainedValue::Tuple(vec![]));
        res
    }

    /// iterates over every instruction in the function's code block and evaluates it.
    /// if a new code block is hit (via mask, repeat, or call instructions) then the current blocks state is stored on a call stack while the new code block is evaluated
    pub fn evaluate_function<CS: ConstraintSystem<F>>(
        function: &'a Function,
        state: EvaluatorState<'a, F, G>,
        index: u32,
        cs: &mut CS,
    ) -> Result<ConstrainedValue<F, G>> {
        let mut evaluator = Self {
            call_stack: Vec::new(),
            namespace_id_counter: state.namespace_id,
            state_data: StateData::create_initial_state_data(state, function, Rc::new(Vec::new()), index)?,
        };
        loop {
            match evaluator.state_data.evaluate_block(cs) {
                Ok(Some(Instruction::Call(data))) => {
                    evaluator.setup_call(data, cs)?;
                }
                Ok(Some(Instruction::Mask(data))) => {
                    evaluator.setup_mask(data, cs)?;
                }
                Ok(Some(Instruction::Repeat(data))) => {
                    evaluator.setup_repeat(data, cs)?;
                }
                Ok(Some(e)) => panic!("invalid control instruction: {:?}", e),
                Ok(None) => match evaluator.state_data.parent_instruction {
                    ParentInstruction::Call(data) => {
                        evaluator.finish_call(data)?;
                    }
                    ParentInstruction::Mask(condition) => {
                        evaluator.finish_mask(condition, cs)?;
                    }
                    ParentInstruction::Repeat(iter_variable) => {
                        evaluator.finish_repeat(iter_variable)?;
                    }
                    ParentInstruction::None => {
                        return Ok(evaluator.finish_evaluation());
                    }
                },
                Err(e) => {
                    return Err(anyhow!(
                        "f#{} i#{}: {:?}",
                        evaluator.state_data.function_index,
                        evaluator.state_data.state.instruction_index,
                        e
                    ));
                }
            }
        }
    }
}
/// stores data about the state for scope recursion
struct StateData<'a, F: PrimeField, G: GroupType<F>> {
    /// the arguments passed to the function
    arguments: Rc<Vec<ConstrainedValue<F, G>>>,
    /// the function currently being evaluated
    function: &'a Function,
    function_index: u32,
    /// the instruction that created this scope
    parent_instruction: ParentInstruction<'a>,
    /// the starting instruction index of the scope
    block_start: u32,
    /// the length of the scope
    block_instruction_count: u32,
    /// the state of the scope
    state: EvaluatorState<'a, F, G>,
    /// the value returned by the scope, if anything has been returned yet
    result: Option<ConstrainedValue<F, G>>,
    /// if the code doesnt always execute
    condition: bool,
}

/// implemented this so i could easily debug execution flow
impl<'a, F: PrimeField, G: GroupType<F>> fmt::Debug for StateData<'a, F, G> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "StateData {{
            ...
            function: {{
                ...
                instructions: {:?},
                ...
            }},
            function_index: {},
            instruction: {:?},
            block_start: {},
            block_instruction_count: {},
            state: {{
                ...
                instruction_index: {},
                call_depth: {},
                ...
            }}
            result: {:?},
            condition: {},
        }}",
            self.function.instructions,
            self.function_index,
            self.parent_instruction,
            self.block_start,
            self.block_instruction_count,
            self.state.instruction_index,
            self.state.call_depth,
            self.result,
            self.condition,
        )
    }
}

impl<'a, F: PrimeField, G: GroupType<F>> StateData<'a, F, G> {
    /// creates the initial state at the start of a programs function evaluation step.
    /// the function passed should be main and the index should point to main
    pub fn create_initial_state_data(
        state: EvaluatorState<'a, F, G>,
        function: &'a Function,
        arguments: Rc<Vec<ConstrainedValue<F, G>>>,
        index: u32,
    ) -> Result<Self> {
        Ok(Self {
            arguments,
            function: &function,
            function_index: index,
            block_start: 0,
            block_instruction_count: function.instructions.len() as u32,
            state,
            parent_instruction: ParentInstruction::None,
            result: None,
            condition: true,
        })
    }

    /// evaluates each instruction in a block.
    /// if a control instruction was hit (mask, repeat, call) then it halts evaluation and returns the instruction
    pub fn evaluate_block<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Result<Option<&'a Instruction>> {
        while self.state.instruction_index < self.block_start + self.block_instruction_count {
            let instruction = &self.function.instructions[self.state.instruction_index as usize];
            match self.evaluate_instruction(instruction, cs)? {
                ControlFlow::Recurse(ins) => return Ok(Some(ins)),
                ControlFlow::Return => {
                    return Ok(None);
                }
                ControlFlow::Continue => continue,
            }
        }
        Ok(None)
    }

    /// handles the control flow of instruction evaluation.
    /// returns the instruction if mask, call, or repeat was hit; else passes it to state for evaluation
    fn evaluate_instruction<CS: ConstraintSystem<F>>(
        &mut self,
        instruction: &'a Instruction,
        cs: &mut CS,
    ) -> Result<ControlFlow<'a>> {
        match instruction {
            Instruction::Call(_) | Instruction::Mask(_) | Instruction::Repeat(_) => {
                Ok(ControlFlow::Recurse(instruction))
            }
            _ => match self.state.evaluate_instruction(instruction, self.condition, cs) {
                Ok(Some(returned)) => {
                    self.result = Some(returned);
                    Ok(ControlFlow::Return)
                }
                Ok(None) => {
                    self.state.instruction_index += 1;
                    Ok(ControlFlow::Continue)
                }
                Err(e) => Err(e),
            },
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct EvaluatorState<'a, F: PrimeField, G: GroupType<F>> {
    pub program: &'a Program,
    variables: IndexMap<u32, ConstrainedValue<F, G>>,
    call_depth: u32,
    pub parent_variables: IndexMap<u32, ConstrainedValue<F, G>>,
    pub function_index: u32,
    pub instruction_index: u32,
    namespace_id: usize,
}

impl<'a, F: PrimeField, G: GroupType<F>> EvaluatorState<'a, F, G> {
    /// creates a new state with no information other than a reference to the program its evaluating
    pub fn new(program: &'a Program) -> Self {
        Self {
            program,
            variables: IndexMap::new(),
            call_depth: 0,
            parent_variables: IndexMap::new(),
            function_index: 0,
            instruction_index: 0,
            namespace_id: 0,
        }
    }

    pub fn cs<'b, CS: ConstraintSystem<F>>(&'b mut self, cs: &'b mut CS) -> impl ConstraintSystem<F> + 'b {
        let function_index = self.function_index;
        let instruction_index = self.instruction_index;
        let namespace_id = self.namespace_id;
        cs.ns(move || format!("id#{}f#{}i#{}", namespace_id, function_index, instruction_index))
    }

    pub fn cs_meta<'b, CS: ConstraintSystem<F>>(
        &'b mut self,
        meta: &str,
        cs: &'b mut CS,
    ) -> impl ConstraintSystem<F> + 'b {
        let function_index = self.function_index;
        let instruction_index = self.instruction_index;
        let namespace_id = self.namespace_id;
        cs.ns(move || {
            format!(
                "id#{}f#{}i#{}: {}",
                namespace_id, function_index, instruction_index, meta
            )
        })
    }

    fn allocate_input<CS2: ConstraintSystem<F>>(
        cs: &mut CS2,
        type_: &Type,
        name: &str,
        value: Value,
    ) -> Result<ConstrainedValue<F, G>, ValueError> {
        Ok(match type_ {
            Type::Address => Address::from_input(&mut cs.ns(|| name.to_string()), name, value)?,
            Type::Boolean => bool_from_input(&mut cs.ns(|| name.to_string()), name, value)?,
            Type::Field => FieldType::from_input(&mut cs.ns(|| name.to_string()), name, value)?,
            Type::Char => Char::from_input(&mut cs.ns(|| name.to_string()), name, value)?,
            Type::Group => match value {
                Value::Group(g) => {
                    ConstrainedValue::Group(G::constant(&g)?.to_allocated(&mut cs.ns(|| name.to_string()))?)
                }
                _ => {
                    return Err(
                        GroupError::invalid_group("expected group, didn't find group in input".to_string()).into(),
                    );
                }
            },
            Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128 => Integer::from_input(&mut cs.ns(|| name.to_string()), name, value)?,
            Type::Array(inner, len) => {
                let values = match value {
                    Value::Array(x) => x,
                    value => return Err(ValueError::bad_value_for_type(&*type_.to_string(), &*value.to_string())),
                };
                if values.len() != len.unwrap() as usize {
                    return Err(ValueError::bad_value_for_type(
                        &*type_.to_string(),
                        &*format!("array of length {}", values.len()),
                    ));
                }
                let mut out = Vec::with_capacity(values.len());
                for (i, value) in values.into_iter().enumerate() {
                    out.push(Self::allocate_input(
                        &mut cs.ns(|| format!("{}[{}]", name, i)),
                        &**inner,
                        name,
                        value,
                    )?);
                }
                ConstrainedValue::Array(out)
            }
            Type::Tuple(inner) => {
                let values = match value {
                    Value::Tuple(x) => x,
                    value => return Err(ValueError::bad_value_for_type(&*type_.to_string(), &*value.to_string())),
                };
                if values.len() != inner.len() {
                    return Err(ValueError::bad_value_for_type(
                        &*type_.to_string(),
                        &*format!("tuple of length {}", values.len()),
                    ));
                }
                let mut out = Vec::with_capacity(values.len());
                for (i, (value, type_)) in values.into_iter().zip(inner.iter()).enumerate() {
                    out.push(Self::allocate_input(
                        &mut cs.ns(|| format!("{}.{}", name, i)),
                        type_,
                        name,
                        value,
                    )?);
                }
                ConstrainedValue::Tuple(out)
            }
            Type::Circuit(_) => return Err(ValueError::incompatible_types("cannot have circuit input")),
        })
    }

    pub fn resolve<'b, CS: ConstraintSystem<F>>(
        &'b mut self,
        value: &Value,
        cs: &'b mut CS,
    ) -> Result<Cow<'b, ConstrainedValue<F, G>>> {
        Ok(Cow::Owned(match value {
            Value::Address(bytes) => ConstrainedValue::Address(Address::constant(&bytes[..])?),
            Value::Boolean(value) => ConstrainedValue::Boolean(Boolean::Constant(*value)),
            Value::Field(limbs) => ConstrainedValue::Field(FieldType::constant(cs, &limbs)?),
            Value::Char(c) => ConstrainedValue::Char(Char::constant(cs, *c)?),
            Value::Group(g) => ConstrainedValue::Group(G::constant(g)?),
            Value::Integer(i) => ConstrainedValue::Integer(Integer::constant(i)?),
            Value::Array(items) => {
                let mut out = Vec::with_capacity(items.len());
                // todo: optionally check inner types
                for item in items {
                    out.push(self.resolve(item, cs)?.into_owned());
                }
                ConstrainedValue::Array(out)
            }
            Value::Tuple(items) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    out.push(self.resolve(item, cs)?.into_owned());
                }
                ConstrainedValue::Tuple(out)
            }
            Value::Str(_) => return Err(anyhow!("cannot have resolved control string")),
            Value::Ref(i) => {
                return Ok(Cow::Borrowed(
                    self.variables
                        .get(i)
                        .or(self.parent_variables.get(i))
                        // .expect("reference to unknown variable")
                        .ok_or_else(|| anyhow!("reference to unknown variable"))?,
                ));
            }
        }))
    }

    pub fn store(&mut self, variable: u32, value: ConstrainedValue<F, G>) {
        self.variables.insert(variable, value);
    }

    pub fn handle_input_block<CS: ConstraintSystem<F>>(
        &mut self,
        name: &str,
        input_header: &[IrInput],
        input_values: &IndexMap<String, Value>,
        cs: &mut CS,
    ) -> Result<()> {
        let mut cs = cs.ns(|| format!("input {}", name));
        for ir_input in input_header {
            let value = input_values
                .get(&ir_input.name)
                .ok_or_else(|| anyhow!("missing input value for '{}'", ir_input.name))?;
            if !value.matches_input_type(&ir_input.type_) {
                return Err(anyhow!(
                    "type mismatch for input '{}', expected {}",
                    ir_input.name,
                    ir_input.type_
                ));
            }
            let value = Self::allocate_input(&mut cs, &ir_input.type_, &*ir_input.name, value.clone())?;
            self.variables.insert(ir_input.variable, value);
        }
        Ok(())
    }

    pub fn handle_const_input_block<CS: ConstraintSystem<F>>(
        &mut self,
        input_header: &[IrInput],
        input_values: &IndexMap<String, Value>,
        cs: &mut CS,
    ) -> Result<()> {
        for ir_input in input_header {
            let value = input_values
                .get(&ir_input.name)
                .ok_or_else(|| anyhow!("missing input value for '{}'", ir_input.name))?;
            if !value.matches_input_type(&ir_input.type_) {
                return Err(anyhow!(
                    "type mismatch for input '{}', expected {}",
                    ir_input.name,
                    ir_input.type_
                ));
            }
            let value = self.resolve(value, cs)?.into_owned();
            self.variables.insert(ir_input.variable, value);
        }
        Ok(())
    }

    /// loads the arguments for a function into the states variable list
    pub fn setup_evaluate_function(
        &mut self,
        index: u32,
        arguments: &[ConstrainedValue<F, G>],
    ) -> Result<&'a Function> {
        let function = self.program.functions.get(index as usize).expect("missing function");

        let mut arg_register = function.argument_start_variable;
        for argument in arguments {
            self.variables.insert(arg_register, argument.clone());
            arg_register += 1;
        }

        self.function_index = index;
        self.instruction_index = 0;
        self.call_depth += 1;

        Ok(&function)
    }
}
