use super::*;

pub const LEN_CORE: &str = "len";

impl<'a, F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>> EvaluatorState<'a, F, G, CS> {
    pub fn call_core_len(&mut self, arguments: &[ConstrainedValue<F, G>]) -> Result<ConstrainedValue<F, G>> {
        match arguments.get(0) {
            Some(ConstrainedValue::Array(array)) => Ok(ConstrainedValue::Integer(Integer::new(&IrInteger::U32(
                array.len() as u32,
            )))),
            Some(v) => Err(ValueError::incompatible_types(&format!("{}.len()", v)).into()),
            None => Err(anyhow!("illegal `len` call, expected 1 argument")),
        }
    }
}
