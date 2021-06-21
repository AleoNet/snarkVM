use snarkvm_fields::PrimeField;
use snarkvm_r1cs::ConstraintSystem;

use crate::{errors::ValueError, ConstrainedValue, GroupType};

pub fn enforce_negate<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    value: ConstrainedValue<F, G>,
) -> Result<ConstrainedValue<F, G>, ValueError> {
    match value {
        ConstrainedValue::Integer(integer) => Ok(ConstrainedValue::Integer(integer.negate(cs)?)),
        ConstrainedValue::Field(field) => Ok(ConstrainedValue::Field(field.negate(cs)?)),
        ConstrainedValue::Group(group) => Ok(ConstrainedValue::Group(group.negate(cs)?)),
        value => Err(ValueError::incompatible_types(&*format!("-{}", value))),
    }
}
