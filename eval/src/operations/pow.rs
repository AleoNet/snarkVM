use snarkvm_fields::PrimeField;
use snarkvm_r1cs::ConstraintSystem;

use crate::{errors::ValueError, ConstrainedValue, GroupType};

pub fn enforce_pow<F: PrimeField, G: GroupType<F>, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    left: ConstrainedValue<F, G>,
    right: ConstrainedValue<F, G>,
) -> Result<ConstrainedValue<F, G>, ValueError> {
    match (left, right) {
        (ConstrainedValue::Integer(num_1), ConstrainedValue::Integer(num_2)) => {
            Ok(ConstrainedValue::Integer(num_1.pow(cs, num_2)?))
        }
        (val_1, val_2) => Err(ValueError::incompatible_types(&*format!("{} ** {}", val_1, val_2,))),
    }
}
