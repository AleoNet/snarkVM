use snarkvm_fields::PrimeField;
use snarkvm_gadgets::boolean::Boolean;
use snarkvm_r1cs::ConstraintSystem;

use crate::{errors::ValueError, ConstrainedValue, GroupType};

pub fn enforce_or<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    left: ConstrainedValue<F, G>,
    right: ConstrainedValue<F, G>,
) -> Result<ConstrainedValue<F, G>, ValueError> {
    let name = format!("{} || {}", left, right);

    if let (ConstrainedValue::Boolean(left_bool), ConstrainedValue::Boolean(right_bool)) = (left, right) {
        let result = Boolean::or(cs.ns(|| name.clone()), &left_bool, &right_bool)
            .map_err(|e| ValueError::cannot_enforce("||", e))?;

        return Ok(ConstrainedValue::Boolean(result));
    }

    Err(ValueError::incompatible_types(&*name))
}
