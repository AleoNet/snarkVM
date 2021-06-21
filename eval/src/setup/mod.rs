use std::{borrow::Cow, convert::TryInto};

use anyhow::*;
use indexmap::IndexMap;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    integers::{UInt16, UInt32, UInt8},
    Boolean,
    CondSelectGadget,
    Integer as IntegerTrait,
};
use snarkvm_ir::{Input as IrInput, Instruction, MaskData, Program, RepeatData, Type, Value};
use snarkvm_r1cs::ConstraintSystem;

use crate::{
    errors::{GroupError, ValueError},
    Address,
    Char,
    ConstrainedValue,
    Evaluator,
    FieldType,
    GroupType,
    Input,
    Integer,
    IntegerType,
};

mod instruction;

pub struct SetupEvaluator<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> {
    cs: CS,
    variables: IndexMap<u32, ConstrainedValue<F, G>>,
}

struct EvaluatorState<'a> {
    program: &'a Program,
    call_depth: usize,
}

impl<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> SetupEvaluator<F, G, CS> {
    pub fn new(cs: CS) -> Self {
        Self {
            cs,
            variables: IndexMap::new(),
        }
    }

    fn allocate_input(&mut self, type_: &Type, name: &str, value: Value) -> Result<ConstrainedValue<F, G>, ValueError> {
        Ok(match type_ {
            Type::Address => Address::from_input(&mut self.cs, name, value)?,
            Type::Boolean => todo!(),
            Type::Field => FieldType::from_input(&mut self.cs, name, value)?,
            Type::Char => Char::from_input(&mut self.cs, name, value)?,
            Type::Group => match value {
                Value::Group(g) => ConstrainedValue::Group(G::constant(&g)?.to_allocated(&mut self.cs)?),
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
            | Type::I128 => Integer::from_input(&mut self.cs, name, value)?,
            Type::Array(_, _) => todo!(),
            Type::Tuple(_) => todo!(),
            Type::Circuit(_) => todo!(),
        })
    }

    fn resolve<'a>(&'a mut self, value: &Value) -> Result<Cow<'a, ConstrainedValue<F, G>>> {
        Ok(Cow::Owned(match value {
            Value::Address(bytes) => ConstrainedValue::Address(Address::constant(&bytes[..])?),
            Value::Boolean(value) => ConstrainedValue::Boolean(Boolean::Constant(*value)),
            Value::Field(limbs) => ConstrainedValue::Field(FieldType::constant(&mut self.cs, &limbs[..])?),
            Value::Char(c) => ConstrainedValue::Char(Char::constant(&mut self.cs, *c, &[*c as u64])?),
            Value::Group(g) => ConstrainedValue::Group(G::constant(g)?),
            Value::Integer(i) => ConstrainedValue::Integer(Integer::constant(i)?),
            Value::Array(items) => {
                let mut out = Vec::with_capacity(items.len());
                // todo: check inner types?
                for item in items {
                    out.push(self.resolve(item)?.into_owned());
                }
                ConstrainedValue::Array(out)
            }
            Value::Tuple(items) => {
                let mut out = Vec::with_capacity(items.len());
                for item in items {
                    out.push(self.resolve(item)?.into_owned());
                }
                ConstrainedValue::Tuple(out)
            }
            Value::Str(_) => return Err(anyhow!("cannot have resolved control string")),
            Value::Ref(i) => {
                return Ok(Cow::Borrowed(
                    self.variables
                        .get(i)
                        .ok_or_else(|| anyhow!("reference to unknown variable"))?,
                ));
            }
        }))
    }

    fn handle_input_block(&mut self, input_header: &[IrInput], input_values: &IndexMap<String, Value>) -> Result<()> {
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
            let value = self.allocate_input(&ir_input.type_, &*ir_input.name, value.clone())?;
            self.variables.insert(ir_input.variable, value);
        }
        Ok(())
    }

    fn evaluate_function<'a>(
        &mut self,
        state: &mut EvaluatorState<'a>,
        index: usize,
        arguments: &[ConstrainedValue<F, G>],
    ) -> Result<ConstrainedValue<F, G>> {
        let function = state.program.functions.get(index).expect("missing function");
        //todo: scope variables for recursion
        let mut arg_register = function.argument_start_variable;
        for argument in arguments {
            self.variables.insert(arg_register, argument.clone());
            arg_register += 1;
        }
        let mut result = ConstrainedValue::<F, G>::Tuple(vec![]);
        self.evaluate_block(state, &function.instructions[..], &mut result)?;
        Ok(result)
    }

    fn evaluate_block<'a>(
        &mut self,
        state: &mut EvaluatorState<'a>,
        block: &[Instruction],
        mut result: &mut ConstrainedValue<F, G>,
    ) -> Result<()> {
        let mut instruction_index = 0usize;
        while instruction_index < block.len() {
            let instruction = &block[instruction_index];
            match instruction {
                Instruction::Mask(MaskData {
                    instruction_count,
                    condition,
                }) => {
                    let instruction_count = *instruction_count as usize;
                    if instruction_count + instruction_index >= block.len() {
                        return Err(anyhow!("illegal mask block length"));
                    }

                    let condition = self.resolve(condition)?.into_owned();
                    let condition = condition
                        .extract_bool()
                        .map_err(|value| anyhow!("illegal condition type for conditional block: {}", value))?;
                    instruction_index += 1;
                    //todo: shield variables
                    let mut interior = result.clone();
                    self.evaluate_block(
                        state,
                        &block[instruction_index..instruction_index + instruction_count],
                        &mut interior,
                    )?;
                    instruction_index += instruction_count;
                    let prior_result = result.clone();
                    *result =
                        ConstrainedValue::conditionally_select(&mut self.cs, condition, &interior, &prior_result)?;
                    continue;
                }
                Instruction::Repeat(RepeatData {
                    instruction_count,
                    iter_variable,
                    from,
                    to,
                }) => {
                    let instruction_count = *instruction_count as usize;
                    if instruction_count + instruction_index >= block.len() {
                        return Err(anyhow!("illegal repeat block length"));
                    }

                    let from = self.resolve(from)?.into_owned();
                    let from_int = from
                        .extract_integer()
                        .map_err(|value| anyhow!("illegal type for loop init: {}", value))?
                        .to_owned();
                    let from = from_int
                        .to_usize()
                        .ok_or_else(|| anyhow!("illegal input-derived loop index"))?;

                    let to = self.resolve(to)?.into_owned();
                    let to = to
                        .extract_integer()
                        .map_err(|value| anyhow!("illegal type for loop terminator: {}", value))?
                        .to_usize()
                        .ok_or_else(|| anyhow!("illegal input-derived loop terminator"))?;
                    if from < to {
                        // todo: should this be an error
                    }
                    instruction_index += 1;
                    //todo: max loop count (DOS vector)
                    for i in from..to {
                        self.variables.insert(
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
                        self.evaluate_block(
                            state,
                            &block[instruction_index..instruction_index + instruction_count],
                            &mut result,
                        )?;
                    }
                    instruction_index += instruction_count as usize;
                    continue;
                }
                instruction => {
                    if let Some(returned) = self.evaluate_instruction(state, instruction)? {
                        *result = returned;
                        return Ok(());
                    }
                }
            }

            instruction_index += 1;
        }
        Ok(())
    }
}

impl<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> Evaluator<F, G> for SetupEvaluator<F, G, CS> {
    type Error = anyhow::Error;
    type Output = ConstrainedValue<F, G>;

    fn evaluate(&mut self, program: &Program, input: &Input) -> Result<Self::Output, Self::Error> {
        self.handle_input_block(&program.header.main_inputs, &input.main)?;
        self.handle_input_block(&program.header.constant_inputs, &input.constants)?; //todo: should these not allocate?
        self.handle_input_block(&program.header.register_inputs, &input.registers)?;
        self.handle_input_block(&program.header.public_states, &input.public_states)?;
        self.handle_input_block(&program.header.private_record_states, &input.private_record_states)?;
        self.handle_input_block(&program.header.private_leaf_states, &input.private_leaf_states)?;

        let mut state = EvaluatorState { program, call_depth: 0 };
        let output = self.evaluate_function(&mut state, 0, &[])?; // arguments assigned via input system for entrypoint
        Ok(output)
    }
}
