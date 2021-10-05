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

use snarkvm_ir::{CallData, Function};

use super::*;

#[derive(Debug)]
enum FunctionReturn<'a> {
    ControlFlow(bool),
    Recurse(&'a Instruction),
}
#[derive(Debug)]
struct CallStateData<'a, 'b, F: PrimeField, G: GroupType<F>> {
    function: &'b Function,
    function_index: usize,
    instruction_index: usize,
    state: EvaluatorState<'a, F, G>,
    destination: Option<u32>,
}

impl<'a, 'b, F: PrimeField, G: GroupType<F>> CallStateData<'a, 'b, F, G> {
    pub fn evaluate_block<CS: ConstraintSystem<F>>(
        &mut self,
        base_instruction_index: usize,
        result: &mut Option<ConstrainedValue<F, G>>,
        cs: &mut CS,
    ) -> Result<Option<&'b Instruction>> {
        // let mut instruction_index = 0usize;
        while self.instruction_index < self.function.instructions.len() {
            let instruction = &self.function.instructions[self.instruction_index];
            self.instruction_index = self.instruction_index + base_instruction_index;
            match self.evaluate_control_instruction(base_instruction_index, instruction, result, cs)? {
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
        base_instruction_index: usize,
        instruction: &'b Instruction,
        result: &mut Option<ConstrainedValue<F, G>>,
        cs: &mut CS,
    ) -> Result<FunctionReturn<'b>> {
        match instruction {
            Instruction::Mask(MaskData {
                instruction_count,
                condition,
            }) => {
                let instruction_count = *instruction_count as usize;
                if instruction_count + self.instruction_index >= self.function.instructions.len() {
                    return Err(anyhow!("illegal mask block length"));
                }

                let condition = self.state.resolve(condition, cs)?.into_owned();
                let condition = condition
                    .extract_bool()
                    .map_err(|value| anyhow!("illegal condition type for conditional block: {}", value))?;
                self.instruction_index += 1;

                let mut interior = result.clone();
                todo!();
                // let mut assignments = HashMap::new();
                // let child_result = self.child(
                //     &*format!("{}: conditional block", self.instruction_index),
                //     |state| {
                //         state.evaluate_block(
                //             base_instruction_index + *instruction_index,
                //             instruction_index,
                //             &block[*instruction_index..*instruction_index + instruction_count],
                //             &mut interior,
                //             cs,
                //         )
                //     },
                //     &mut assignments,
                // );
                // if child_result.is_err() && condition.get_value().unwrap_or(true) {
                //     match child_result {
                //         Ok(e) => panic!("expected err"),
                //         Err(e) => return Err(e),
                //     }
                // }
                // for (variable, value) in assignments {
                //     if let Some(prior) = self
                //         .state
                //         .variables
                //         .get(&variable)
                //         .or(self.state.parent_variables.get(&variable))
                //     {
                //         let prior = prior.clone(); //todo: optimize away clone
                //         let value = ConstrainedValue::conditionally_select(
                //             &mut self.state.cs_meta(&*format!("selection {}", variable), cs),
                //             condition,
                //             &value,
                //             &prior,
                //         )?;
                //         self.state.store(variable, value);
                //     } else {
                //         // if it didnt exist in parent scope before, it cant exist now
                //         // self.store(variable, value);
                //     }
                // }

                self.instruction_index += instruction_count;
                match (result.clone(), interior) {
                    (Some(prior), Some(interior)) => {
                        *result = Some(ConstrainedValue::conditionally_select(
                            &mut self.state.cs_meta(&*format!("selection result"), cs),
                            condition,
                            &interior,
                            &prior,
                        )?);
                    }
                    (None, Some(interior)) => {
                        // will produce garbage if invalid IR (incomplete return path)
                        *result = Some(interior);
                    }
                    (_, None) => (),
                }
            }
            Instruction::Repeat(RepeatData {
                instruction_count,
                iter_variable,
                inclusive,
                from,
                to,
            }) => {
                let instruction_count = *instruction_count as usize;
                if instruction_count + self.instruction_index >= self.function.instructions.len() {
                    return Err(anyhow!("illegal repeat block length"));
                }

                let from = self.state.resolve(from, cs)?.into_owned();
                let from_int = from
                    .extract_integer()
                    .map_err(|value| anyhow!("illegal type for loop init: {}", value))?
                    .to_owned();
                let from = from_int
                    .to_usize()
                    .ok_or_else(|| anyhow!("illegal input-derived loop index"))?;

                let to = self.state.resolve(to, cs)?.into_owned();
                let to = to
                    .extract_integer()
                    .map_err(|value| anyhow!("illegal type for loop terminator: {}", value))?
                    .to_usize()
                    .ok_or_else(|| anyhow!("illegal input-derived loop terminator"))?;

                let iter: Box<dyn Iterator<Item = usize>> = match (from < to, inclusive) {
                    (true, true) => Box::new(from..=to),
                    (true, false) => Box::new(from..to),
                    (false, true) => Box::new((to..=from).rev()),
                    // add the range to the values to get correct bound
                    (false, false) => Box::new(((to + 1)..(from + 1)).rev()),
                };

                self.instruction_index += 1;
                //todo: max loop count (DOS vector)
                for i in iter {
                    self.state.variables.insert(
                        *iter_variable,
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

                    let mut assignments = HashMap::new();

                    todo!();
                    // self.child(
                    //     &*format!("{}: iteration #{}", self.instruction_index, i),
                    //     |state| {
                    //         state.evaluate_block(
                    //             base_instruction_index + *instruction_index,
                    //             instruction_index,
                    //             &block[*instruction_index..*instruction_index + instruction_count],
                    //             &mut result,
                    //             cs,
                    //         )
                    //     },
                    //     &mut assignments,
                    // )?;

                    for (variable, value) in assignments {
                        self.state.store(variable, value);
                    }
                }
                self.instruction_index += instruction_count as usize;
            }
            instruction => {
                match self.state.evaluate_instruction(instruction, cs) {
                    Ok(InstructionReturn::Value(Some(returned))) => {
                        *result = Some(returned);
                        return Ok(FunctionReturn::ControlFlow(true));
                    }
                    Ok(InstructionReturn::Value(None)) => (),
                    Ok(InstructionReturn::Recurse(i)) => return Ok(FunctionReturn::Recurse(i)),
                    Err(e) => {
                        return Err(anyhow!(
                            "i#{}: {:?}",
                            self.instruction_index + base_instruction_index,
                            e
                        ))
                    }
                }
                self.instruction_index += 1;
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

    pub fn child<T, E, I: FnMut(&mut EvaluatorState<'a, F, G>) -> Result<T, E>>(
        &mut self,
        name: &str,
        mut inner: I,
        merge: &mut HashMap<u32, ConstrainedValue<F, G>>,
    ) -> Result<T, E> {
        let mut state = EvaluatorState {
            program: self.program,
            variables: HashMap::new(),
            call_depth: self.call_depth,
            parent_variables: self.variables.clone().union(self.parent_variables.clone()), // todo: eval perf of im::map here
            function_index: self.function_index,
            instruction_index: self.instruction_index,
        };
        let out = inner(&mut state)?;
        *merge = state.variables;
        Ok(out)
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
        index: usize,
        arguments: &[ConstrainedValue<F, G>],
        cs: &mut CS,
    ) -> Result<ConstrainedValue<F, G>> {
        let mut call_stack = Vec::new();
        let function = self.setup_evaluate_function(index, arguments)?;
        let mut state_data = CallStateData {
            function: &function,
            instruction_index: 0,
            function_index: index,
            state: self,
            destination: None,
        };
        loop {
            // todo: figure out results?
            let mut result = None;
            let function_idx = state_data.function_index;
            // TODO FIGURE OUT SUB BLOCK STUFF IFS/LOOPS
            match state_data
                .evaluate_block(0, &mut result, cs)
                .map_err(|e| anyhow!("f#{}: {:?}", function_idx, e))?
            {
                Some(Instruction::Call(CallData {
                    destination,
                    index,
                    arguments,
                })) => {
                    let arguments = arguments
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
                        instruction_index: state_data.state.instruction_index,
                    };

                    let function = state.setup_evaluate_function(*index as usize, &arguments)?;
                    call_stack.push(state_data);
                    state_data = CallStateData {
                        function: &function,
                        instruction_index: 0,
                        function_index: *index as usize,
                        state,
                        destination: Some(*destination),
                    };
                }
                None => {
                    let res = result.unwrap_or_else(|| ConstrainedValue::Tuple(vec![]));
                    if let Some(old_state_data) = call_stack.pop() {
                        state_data = old_state_data;
                        if let Some(d) = state_data.destination {
                            state_data.state.store(d, res);
                        } else {
                            panic!("todo: no dest")
                        }
                    } else {
                        return Ok(res);
                    }
                }
                Some(e) => panic!("todo: bad ins ret: {}", e),
            }
        }
    }

    pub fn setup_evaluate_function(
        &mut self,
        index: usize,
        arguments: &[ConstrainedValue<F, G>],
    ) -> Result<&'a Function> {
        let function = self.program.functions.get(index).expect("missing function");

        let mut arg_register = function.argument_start_variable;
        for argument in arguments {
            self.variables.insert(arg_register, argument.clone());
            arg_register += 1;
        }

        self.function_index = index as u32;
        self.instruction_index = 0;
        self.call_depth += 1;

        if self.call_depth > self.program.header.inline_limit {
            return Err(anyhow!("f#{}: max inline limit hit", index));
        }
        Ok(&function)
    }
}
