use std::convert::TryInto;

use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{
    integers::{UInt16, UInt32, UInt8},
    CondSelectGadget,
    EvaluateEqGadget,
    Integer as IntegerTrait,
};
use snarkvm_ir::{ArrayInitRepeatData, CallData, Instruction, PredicateData, QueryData, Value, VarData};
use snarkvm_r1cs::ConstraintSystem;

use crate::{
    errors::{ArrayError, ValueError},
    operations,
    ConstrainedValue,
    GroupType,
    Integer,
    SetupEvaluator,
};

use anyhow::*;

use super::EvaluatorState;

impl<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> SetupEvaluator<F, G, CS> {
    fn resolve_binary(&mut self, data: &QueryData<2>) -> Result<(ConstrainedValue<F, G>, ConstrainedValue<F, G>)> {
        let left = self.resolve(data.values.get(0).unwrap())?.into_owned();
        let right = self.resolve(data.values.get(1).unwrap())?.into_owned();
        Ok((left, right))
    }

    pub(super) fn evaluate_instruction<'a>(
        &mut self,
        state: &mut EvaluatorState<'a>,
        instruction: &Instruction,
    ) -> Result<Option<ConstrainedValue<F, G>>> {
        match instruction {
            Instruction::Add(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::enforce_add(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Sub(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::enforce_sub(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Mul(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::enforce_mul(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Div(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::enforce_div(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Pow(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::enforce_pow(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Or(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::enforce_or(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::And(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::enforce_and(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Eq(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::evaluate_eq(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Ne(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::evaluate_not(operations::evaluate_eq(&mut self.cs, left, right)?)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Ge(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::evaluate_ge(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Gt(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::evaluate_gt(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Le(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::evaluate_le(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::Lt(data) => {
                let (left, right) = self.resolve_binary(data)?;
                let out = operations::evaluate_lt(&mut self.cs, left, right)?;
                self.variables.insert(data.destination, out);
            }
            Instruction::BitOr(_) => todo!(),
            Instruction::BitAnd(_) => todo!(),
            Instruction::BitXor(_) => todo!(),
            Instruction::Shr(_) => todo!(),
            Instruction::ShrSigned(_) => todo!(),
            Instruction::Shl(_) => todo!(),
            Instruction::Mod(_) => todo!(),
            Instruction::Not(QueryData { destination, values }) => {
                let inner = self.resolve(values.get(0).unwrap())?.into_owned();
                let out = operations::evaluate_not(inner)?;
                self.variables.insert(*destination, out);
            }
            Instruction::Negate(QueryData { destination, values }) => {
                let inner = self.resolve(values.get(0).unwrap())?.into_owned();
                let out = operations::enforce_negate(&mut self.cs, inner)?;
                self.variables.insert(*destination, out);
            }
            Instruction::BitNot(_) => todo!(),
            Instruction::ArrayInitRepeat(ArrayInitRepeatData {
                destination,
                length,
                value,
            }) => {
                let inner = self.resolve(value)?.into_owned();
                // todo: max array length (DOS vector)
                let array = ConstrainedValue::Array(vec![inner; *length as usize]);
                self.variables.insert(*destination, array);
            }
            Instruction::ArrayInit(VarData { destination, values }) => {
                let mut inner = Vec::with_capacity(values.len());
                for value in values {
                    inner.push(self.resolve(value)?.into_owned());
                }
                //todo: assert same type and flatten array if needed
                let array = ConstrainedValue::Array(inner);
                self.variables.insert(*destination, array);
            }
            Instruction::ArrayIndexGet(QueryData { destination, values }) => {
                let index = self.resolve(values.get(1).unwrap())?.into_owned();
                let array = self.resolve(values.get(0).unwrap())?;
                let index_resolved = index
                    .extract_integer()
                    .map_err(|value| anyhow!("invalid value for array index: {}", value))?;
                let array = array
                    .extract_array()
                    .map_err(|value| anyhow!("invalid array for array index: {}", value))?;
                let out = if let Some(index) = index_resolved.to_usize() {
                    if index >= array.len() {
                        return Err(ArrayError::array_index_out_of_bounds(index, array.len()).into());
                    }
                    array.get(index).cloned().unwrap()
                } else if array.is_empty() {
                    return Err(ArrayError::array_index_out_of_bounds(0, 0).into());
                } else {
                    let mut array = array.clone();
                    let mut current_value = array.pop().unwrap();
                    for (i, item) in array.into_iter().enumerate() {
                        let namespace_string = format!("evaluate array access eq {}", i);
                        let eq_namespace = self.cs.ns(|| namespace_string);

                        let i = match &index_resolved {
                            Integer::U8(_) => Integer::U8(UInt8::constant(
                                i.try_into()
                                    .map_err(|_| ArrayError::array_index_out_of_legal_bounds())?,
                            )),
                            Integer::U16(_) => Integer::U16(UInt16::constant(
                                i.try_into()
                                    .map_err(|_| ArrayError::array_index_out_of_legal_bounds())?,
                            )),
                            Integer::U32(_) => Integer::U32(UInt32::constant(
                                i.try_into()
                                    .map_err(|_| ArrayError::array_index_out_of_legal_bounds())?,
                            )),
                            _ => return Err(ArrayError::invalid_index(index_resolved.get_type().to_string()).into()),
                        };
                        let index_comparison = index_resolved
                            .evaluate_equal(eq_namespace, &i)
                            .map_err(|e| ValueError::cannot_enforce("==", e))?;

                        let unique_namespace = self.cs.ns(|| format!("select array access {}", i));
                        let value = ConstrainedValue::conditionally_select(
                            unique_namespace,
                            &index_comparison,
                            &item,
                            &current_value,
                        )
                        .map_err(|e| ValueError::cannot_enforce("conditional select", e))?;
                        current_value = value;
                    }
                    current_value
                };
                self.variables.insert(*destination, out);
            }
            Instruction::ArraySliceGet(QueryData { destination, values }) => {
                let array = self.resolve(values.get(0).unwrap())?.into_owned();
                let array = array
                    .extract_array()
                    .map_err(|value| anyhow!("illegal value for array slice: {}", value))?;
                let start = self.resolve(values.get(1).unwrap())?.into_owned();
                let start_resolved = start
                    .extract_integer()
                    .map_err(|value| anyhow!("invalid value for array slice start index: {}", value))?;
                let stop = self.resolve(values.get(2).unwrap())?.into_owned();
                let stop_resolved = stop
                    .extract_integer()
                    .map_err(|value| anyhow!("invalid value for array slice end index: {}", value))?;

                todo!();
                //self.variables.insert(*destination, out);
            }
            Instruction::ArrayIndexStore(_) => todo!(),
            Instruction::ArraySliceStore(_) => todo!(),
            Instruction::TupleInit(VarData { destination, values }) => {
                let mut inner = Vec::with_capacity(values.len());
                for value in values {
                    inner.push(self.resolve(value)?.into_owned());
                }
                let array = ConstrainedValue::Tuple(inner);
                self.variables.insert(*destination, array);
            }
            Instruction::TupleIndexGet(QueryData { destination, values }) => {
                let index = self
                    .resolve(values.get(1).unwrap())?
                    .extract_integer()
                    .map_err(|value| anyhow!("invalid index type for tuple index: {}", value))?
                    .to_usize()
                    .ok_or_else(|| anyhow!("illegal variable input for tuple index"))?;

                let tuple = self.resolve(values.get(0).unwrap())?;
                let tuple = tuple
                    .extract_tuple()
                    .map_err(|value| anyhow!("invalid tuple type for tuple index: {}", value))?;

                let out = tuple
                    .get(index)
                    .ok_or_else(|| {
                        anyhow!(
                            "illegal index {} into tuple of length {} for tuple index",
                            index,
                            tuple.len()
                        )
                    })?
                    .clone();

                self.variables.insert(*destination, out);
            }
            Instruction::TupleIndexStore(QueryData { destination, values }) => {
                let index = self
                    .resolve(values.get(0).unwrap())?
                    .extract_integer()
                    .map_err(|value| anyhow!("invalid index type for tuple store: {}", value))?
                    .to_usize()
                    .ok_or_else(|| anyhow!("illegal variable input for tuple store"))?;

                let tuple = self.resolve(&Value::Ref(*destination))?.into_owned();
                let mut tuple = tuple
                    .extract_tuple()
                    .map_err(|value| anyhow!("invalid tuple type for tuple store: {}", value))?
                    .clone();

                let tuple_len = tuple.len();
                let out = tuple.get_mut(index).ok_or_else(|| {
                    anyhow!(
                        "illegal index {} into tuple of length {} for tuple store",
                        index,
                        tuple_len
                    )
                })?;
                *out = self.resolve(values.get(1).unwrap())?.into_owned();

                self.variables.insert(*destination, ConstrainedValue::Tuple(tuple));
            }
            Instruction::Pick(QueryData { destination, values }) => {
                let condition = self.resolve(values.get(0).unwrap())?.into_owned();
                let condition = condition
                    .extract_bool()
                    .map_err(|value| anyhow!("invalid value for pick condition: {}", value))?;
                let left = self.resolve(values.get(1).unwrap())?.into_owned();
                let right = self.resolve(values.get(2).unwrap())?.into_owned();
                let picked = ConstrainedValue::conditionally_select(&mut self.cs, &condition, &left, &right)?;
                self.variables.insert(*destination, picked);
            }
            Instruction::Mask(_) => {
                panic!("cannot eval mask instructions directly");
            }
            Instruction::Repeat(_) => {
                panic!("cannot eval repeat instructions directly");
            }
            Instruction::Store(QueryData { destination, values }) => {
                let value = self.resolve(values.get(0).unwrap())?.into_owned();
                self.variables.insert(*destination, value);
            }
            Instruction::Call(CallData {
                destination,
                index,
                arguments,
            }) => {
                let arguments = arguments
                    .iter()
                    .map(|x| self.resolve(x).map(|x| x.into_owned()))
                    .collect::<Result<Vec<_>, _>>()?;
                state.call_depth += 1;
                let output = self.evaluate_function(state, *index as usize, &arguments[..]);
                state.call_depth -= 1;
                self.variables.insert(*destination, output?);
            }
            Instruction::Return(PredicateData { values }) => {
                let value = values.get(0).unwrap();
                let value = self.resolve(value)?.into_owned();
                return Ok(Some(value));
            }
            Instruction::Assert(_) => todo!(),
            Instruction::Log(_) => todo!(),
            Instruction::CallCore(_) => todo!(),
        }
        Ok(None)
    }
}
