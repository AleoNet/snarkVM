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

use snarkvm_gadgets::Integer as GadgetInteger;
use snarkvm_gadgets::UInt16;
use snarkvm_gadgets::UInt32;
use snarkvm_gadgets::UInt8;
use snarkvm_ir::{CallData, Function};

use crate::IntegerType;

use super::*;

use std::convert::TryInto;
use std::fmt;

#[derive(Debug)]
enum FunctionReturn<'a> {
    ControlFlow(bool),
    Recurse(&'a Instruction),
}

#[derive(Debug)]
enum ParentInstruction<'a> {
    None,
    Call(&'a CallData),
    Mask(Boolean),
    Repeat(u32),
}

struct CallStateData<'a, 'b, F: PrimeField, G: GroupType<F>> {
    function: &'b Function,
    function_index: u32,
    parent_instruction: ParentInstruction<'b>,
    block_start: u32,
    block_instruction_count: u32,
    state: EvaluatorState<'a, F, G>,
    result: Option<ConstrainedValue<F, G>>,
}

/// implemented this so i could easily debug execution flow
impl<'a, 'b, F: PrimeField, G: GroupType<F>> fmt::Debug for CallStateData<'a, 'b, F, G> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CallStateData {{
            ...
            function: {{
                ...
                instructions: {:?},
                ...
            }},
            instruction: {:?},
            block_start: {},
            block_instruction_count: {},
            state: {{
                ...
                instruction_index: {},
                ...
            }}
        }}",
            self.function.instructions,
            self.parent_instruction,
            self.block_start,
            self.block_instruction_count,
            self.state.instruction_index
        )
    }
}

impl<'a, 'b, F: PrimeField, G: GroupType<F>> CallStateData<'a, 'b, F, G> {
    pub fn evaluate_block<CS: ConstraintSystem<F>>(&mut self, cs: &mut CS) -> Result<Option<&'b Instruction>> {
        while self.state.instruction_index < self.block_start + self.block_instruction_count {
            let instruction = &self.function.instructions[self.state.instruction_index as usize];
            match self.evaluate_control_instruction(instruction, cs)? {
                FunctionReturn::Recurse(ins) => return Ok(Some(ins)),
                FunctionReturn::ControlFlow(true) => {
                    return Ok(None);
                }
                FunctionReturn::ControlFlow(false) => continue,
            }
        }
        Ok(None)
    }

    fn evaluate_control_instruction<CS: ConstraintSystem<F>>(
        &mut self,
        instruction: &'b Instruction,
        cs: &mut CS,
    ) -> Result<FunctionReturn<'b>> {
        match instruction {
            i @ Instruction::Call(_) => return Ok(FunctionReturn::Recurse(i)),
            i @ Instruction::Mask(_) => return Ok(FunctionReturn::Recurse(i)),
            i @ Instruction::Repeat(_) => return Ok(FunctionReturn::Recurse(i)),
            instruction => {
                match self.state.evaluate_instruction(instruction, cs) {
                    Ok(Some(returned)) => {
                        self.result = Some(returned);
                        return Ok(FunctionReturn::ControlFlow(true));
                    }
                    Ok(None) => (),
                    Err(e) => return Err(anyhow!("i#{}: {:?}", self.state.instruction_index, e)),
                }
                self.state.instruction_index += 1;
            }
        }

        Ok(FunctionReturn::ControlFlow(false))
    }
}

#[derive(Clone, Debug)]
pub(super) struct EvaluatorState<'a, F: PrimeField, G: GroupType<F>> {
    pub program: &'a Program,
    variables: HashMap<u32, ConstrainedValue<F, G>>,
    call_depth: u32,
    pub parent_variables: HashMap<u32, ConstrainedValue<F, G>>,
    pub function_index: u32,
    pub instruction_index: u32,
}

impl<'a, F: PrimeField, G: GroupType<F>> EvaluatorState<'a, F, G> {
    pub fn new(program: &'a Program) -> Self {
        Self {
            program,
            variables: HashMap::new(),
            call_depth: 0,
            parent_variables: HashMap::new(),
            function_index: 0,
            instruction_index: 0,
        }
    }

    pub fn cs<'b, CS: ConstraintSystem<F>>(&'b mut self, cs: &'b mut CS) -> impl ConstraintSystem<F> + 'b {
        let function_index = self.function_index;
        let instruction_index = self.instruction_index;
        cs.ns(move || format!("f#{}i#{}", function_index, instruction_index))
    }

    pub fn cs_meta<'b, CS: ConstraintSystem<F>>(
        &'b mut self,
        meta: &str,
        cs: &'b mut CS,
    ) -> impl ConstraintSystem<F> + 'b {
        let function_index = self.function_index;
        let instruction_index = self.instruction_index;
        cs.ns(move || format!("f#{}i#{}: {}", function_index, instruction_index, meta))
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

    pub fn evaluate_function<CS: ConstraintSystem<F>>(
        mut self,
        index: u32,
        arguments: &[ConstrainedValue<F, G>],
        cs: &mut CS,
    ) -> Result<ConstrainedValue<F, G>> {
        let mut call_stack = Vec::new();
        let function = self.setup_evaluate_function(index, arguments)?;
        let mut state_data = CallStateData {
            function: &function,
            function_index: index,
            block_start: 0,
            block_instruction_count: function.instructions.len() as u32,
            state: self,
            parent_instruction: ParentInstruction::None,
            result: None,
        };
        loop {
            match state_data.evaluate_block(cs) {
                Ok(Some(Instruction::Call(data))) => {
                    let arguments = data
                        .arguments
                        .iter()
                        .map(|x| state_data.state.resolve(x, cs).map(|x| x.into_owned()))
                        .collect::<Result<Vec<_>, _>>()?;

                    let mut state = EvaluatorState {
                        program: state_data.state.program,
                        variables: HashMap::new(),
                        call_depth: state_data.state.call_depth,
                        parent_variables: state_data
                            .state
                            .variables
                            .clone()
                            .union(state_data.state.parent_variables.clone()), // todo: eval perf of im::map here
                        function_index: state_data.state.function_index,
                        instruction_index: 0,
                    };

                    let function = state.setup_evaluate_function(data.index, &arguments)?;
                    call_stack.push(state_data);
                    state_data = CallStateData {
                        function: &function,
                        function_index: data.index,
                        block_start: 0,
                        block_instruction_count: function.instructions.len() as u32,
                        state,
                        parent_instruction: ParentInstruction::Call(data),
                        result: None,
                    };
                }
                Ok(Some(Instruction::Mask(data))) => {
                    if data.instruction_count + state_data.state.instruction_index
                        >= state_data.function.instructions.len() as u32
                    {
                        return Err(anyhow!("illegal mask block length"));
                    }

                    let condition = state_data.state.resolve(&data.condition, cs)?.into_owned();
                    let condition = condition
                        .extract_bool()
                        .map_err(|value| anyhow!("illegal condition type for conditional block: {}", value))?
                        .clone();
                    state_data.state.instruction_index += 1;
                    if condition.get_value().unwrap_or(true) {
                        let state = EvaluatorState {
                            program: state_data.state.program,
                            variables: HashMap::new(),
                            call_depth: state_data.state.call_depth,
                            parent_variables: state_data
                                .state
                                .variables
                                .clone()
                                .union(state_data.state.parent_variables.clone()), // todo: eval perf of im::map here
                            function_index: state_data.state.function_index,
                            instruction_index: state_data.state.instruction_index,
                        };
                        let new_state_data = CallStateData {
                            function: state_data.function,
                            function_index: state_data.function_index,
                            block_start: state_data.state.instruction_index,
                            block_instruction_count: data.instruction_count,
                            state,
                            parent_instruction: ParentInstruction::Mask(condition),
                            result: state_data.result.clone(),
                        };
                        state_data.state.instruction_index += data.instruction_count;
                        call_stack.push(state_data);
                        state_data = new_state_data;
                    } else {
                        state_data.state.instruction_index += data.instruction_count
                    }
                }
                Ok(Some(Instruction::Repeat(data))) => {
                    if data.instruction_count + state_data.state.instruction_index
                        >= state_data.function.instructions.len() as u32
                    {
                        return Err(anyhow!("illegal repeat block length"));
                    }

                    let from = state_data.state.resolve(&data.from, cs)?.into_owned();
                    let from_int = from
                        .extract_integer()
                        .map_err(|value| anyhow!("illegal type for loop init: {}", value))?
                        .to_owned();
                    let from = from_int
                        .to_usize()
                        .ok_or_else(|| anyhow!("illegal input-derived loop index"))?;

                    let to = state_data.state.resolve(&data.to, cs)?.into_owned();
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

                    state_data.state.instruction_index += 1;
                    //todo: very memory intensive with large loops since all states get allocated at once
                    let mut iter_state_data = Vec::new();
                    //todo: max loop count (DOS vector)
                    for i in iter {
                        let mut state = EvaluatorState {
                            program: state_data.state.program,
                            variables: HashMap::new(),
                            call_depth: state_data.state.call_depth,
                            parent_variables: state_data
                                .state
                                .variables
                                .clone()
                                .union(state_data.state.parent_variables.clone()), // todo: eval perf of im::map here
                            function_index: state_data.state.function_index,
                            instruction_index: state_data.state.instruction_index,
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
                        let new_state_data = CallStateData {
                            function: state_data.function,
                            function_index: state_data.function_index,
                            block_start: state_data.state.instruction_index,
                            block_instruction_count: data.instruction_count,
                            state,
                            parent_instruction: ParentInstruction::Repeat(data.iter_variable),
                            result: state_data.result.clone(),
                        };
                        iter_state_data.push(new_state_data);
                    }
                    iter_state_data.reverse();
                    state_data.state.instruction_index += data.instruction_count;
                    call_stack.push(state_data);
                    call_stack.extend(iter_state_data.into_iter());
                    state_data = call_stack.pop().unwrap();
                }
                Ok(Some(e)) => panic!("invalid control instruction: {:?}", e),
                Ok(None) => match state_data.parent_instruction {
                    ParentInstruction::None => {
                        let res = state_data.result.unwrap_or_else(|| ConstrainedValue::Tuple(vec![]));
                        return Ok(res);
                    }
                    ParentInstruction::Call(data) => {
                        let res = state_data.result.unwrap_or_else(|| ConstrainedValue::Tuple(vec![]));
                        state_data = call_stack.pop().expect("no state to return to");
                        state_data.state.store(data.destination, res);
                        state_data.state.instruction_index += 1;
                    }
                    ParentInstruction::Mask(condition) => {
                        let assignments = state_data.state.variables;
                        let target_index = state_data.block_start + state_data.block_instruction_count;
                        let result = state_data.result.clone();
                        state_data = call_stack.pop().expect("no state to return to");
                        for (variable, value) in assignments {
                            if let Some(prior) = state_data
                                .state
                                .variables
                                .get(&variable)
                                .or(state_data.state.parent_variables.get(&variable))
                            {
                                let prior = prior.clone(); //todo: optimize away clone
                                let value = ConstrainedValue::conditionally_select(
                                    &mut state_data.state.cs_meta(&*format!("selection {}", variable), cs),
                                    &condition,
                                    &value,
                                    &prior,
                                )?;
                                state_data.state.store(variable, value);
                            } else {
                                // if it didnt exist in parent scope before, it cant exist now
                                // self.store(variable, value);
                            }
                        }
                        assert_eq!(state_data.state.instruction_index, target_index);
                        match (state_data.result.clone(), result.clone()) {
                            (Some(prior), Some(interior)) => {
                                state_data.result = Some(ConstrainedValue::conditionally_select(
                                    &mut state_data.state.cs_meta(&*format!("selection result"), cs),
                                    &condition,
                                    &interior,
                                    &prior,
                                )?);
                            }
                            (None, Some(interior)) => {
                                // will produce garbage if invalid IR (incomplete return path)
                                state_data.result = Some(interior);
                            }
                            (_, None) => (),
                        }
                    }
                    ParentInstruction::Repeat(iter_variable) => {
                        let assignments = state_data.state.variables;
                        state_data = call_stack.pop().expect("no state to return to");
                        for (variable, value) in assignments {
                            if state_data
                                .state
                                .variables
                                .get(&variable)
                                .or(state_data.state.parent_variables.get(&variable))
                                .is_some()
                                && variable != iter_variable
                            {
                                state_data.state.store(variable, value);
                            }
                        }
                    }
                },
                Err(e) => {
                    return Err(anyhow!(
                        "f#{} i#{}: {:?}",
                        state_data.function_index,
                        state_data.state.instruction_index,
                        e
                    ))
                }
            }
        }
    }

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

        if self.call_depth > self.program.header.inline_limit {
            return Err(anyhow!("f#{}: max inline limit hit", index));
        }
        Ok(&function)
    }
}
