use snarkvm_fields::PrimeField;

use crate::{errors::ValueError, ConstrainedValue, GroupType};

pub fn evaluate_not<F: PrimeField, G: GroupType<F>>(
    value: ConstrainedValue<F, G>,
) -> Result<ConstrainedValue<F, G>, ValueError> {
    match value {
        ConstrainedValue::Boolean(boolean) => Ok(ConstrainedValue::Boolean(boolean.not())),
        value => Err(ValueError::incompatible_types(&*format!("!{}", value))),
    }
}
