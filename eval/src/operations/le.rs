use snarkvm_fields::PrimeField;
use snarkvm_gadgets::ComparatorGadget;
use snarkvm_r1cs::ConstraintSystem;

use crate::{errors::ValueError, ConstrainedValue, GroupType};

pub fn evaluate_le<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    left: ConstrainedValue<F, G>,
    right: ConstrainedValue<F, G>,
) -> Result<ConstrainedValue<F, G>, ValueError> {
    let unique_namespace = cs.ns(|| format!("evaluate {} <= {}", left, right));
    let constraint_result = match (left, right) {
        (ConstrainedValue::Integer(num_1), ConstrainedValue::Integer(num_2)) => {
            num_1.less_than_or_equal(unique_namespace, &num_2)
        }
        (val_1, val_2) => {
            return Err(ValueError::incompatible_types(&*format!("{} <= {}", val_1, val_2)));
        }
    };

    let boolean = constraint_result.map_err(|e| ValueError::cannot_enforce("<=", e))?;

    Ok(ConstrainedValue::Boolean(boolean))
}
