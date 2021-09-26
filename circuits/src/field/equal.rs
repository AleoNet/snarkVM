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

use super::*;

impl<E: Environment> Equal for Field<E> {
    type Boolean = Boolean<E>;
    type Output = Result<Self::Boolean>;

    #[named]
    fn eq(&self, other: &Self) -> Self::Output {
        match (self, other) {
            (Field::Constant(a), Field::Constant(b)) => Ok(Boolean::constant(a == b)),
            (Field::Constant(a), Field::Variable(b, cb)) => {
                // let element = b.(&mut cb.borrow_mut().ns(|| function_name!()), &a)?;
                // Ok(Fp::from((element, cb.clone())))
                unimplemented!()
            }
            (Field::Variable(a, cb), Field::Constant(b)) => {
                // let element = a.(&mut cb.borrow_mut().ns(|| function_name!()), &b)?;
                // Ok(Fp::from((element, cb.clone())))
                unimplemented!()
            }
            (Field::Variable(a, cb), Field::Variable(b, _)) => {
                // Allocate the _negation_ of the expected output boolean value as a witness.
                let witness = Boolean::alloc_private(function_name!(), (a != b, cb.clone()))?;
                let witness_variable = match witness.to_gadget_unsafe() {
                    Some(gadget) => gadget.lc(<CB::CS as ConstraintSystem<F>>::one(), F::one()),
                    None => return Err(FieldError::ConstantShouldBeVariable),
                };
                let witness_not_variable = match (&witness).not().to_gadget_unsafe() {
                    Some(gadget) => gadget.lc(<CB::CS as ConstraintSystem<F>>::one(), F::one()),
                    None => return Err(FieldError::ConstantShouldBeVariable),
                };

                // If the witness is `true`, allocate the _inverse_ of (a - b).
                // Else, allocate one.
                let multiplier = Field::alloc_private(
                    function_name!(),
                    (
                        match witness.to_value()? {
                            true => match (self.to_value()? - &other.to_value()?).inverse() {
                                Some(value) => value,
                                _ => return Err(FieldError::MissingValue),
                            },
                            false => Field::<F, CB>::one().to_value()?,
                        },
                        cb.clone(),
                    ),
                )?;
                let multiplier_variable = match multiplier.to_gadget_unsafe() {
                    Some(gadget) => gadget.variable,
                    None => return Err(FieldError::ConstantShouldBeVariable),
                };
                //
                // Equality Enforcement
                // --------------------------------------------------------------
                // Check 1:  (a - b) * multiplier = witness
                // Check 2:  (a - b) * not(witness) = 0
                //
                //
                // Case 1: a == b AND witness == 0 (completeness)
                // --------------------------------------------------------------
                // Check 1:  (a - b) * 1 = 0
                //                 a - b = 0
                // => As a == b, the witness is correct.
                //
                // Check 2:  (a - b) * not(0) = 0
                //                      a - b = 0
                // => As a == b, the witness is correct.
                //
                // Remark: While the multiplier = 1 here, letting multiplier = n,
                //         for n as any field element, also holds.
                //
                //
                // Case 2: a == b AND witness == 1 (soundness)
                // --------------------------------------------------------------
                // Check 1:  (a - b) * 1 = 1
                //                 a - b = 1
                // => As a == b, the witness is incorrect.
                //
                // Remark: While the multiplier = 1 here, letting multiplier = n,
                //         for n as any field element, also holds.
                //
                //
                // Case 3a: a != b AND witness == 0 AND multiplier = 0 (soundness)
                // ----------------------------------------------------------------
                // Check 1:  (a - b) * 0 = 0
                //                     0 = 0
                // => We must rely on Check 2 to enforce correctness.
                //
                // Check 2:  (a - b) * not(0) = 0
                //                      a - b = 0
                // => As a != b, the witness is incorrect.
                //
                //
                // Case 3b: a != b AND witness == 0 AND multiplier = 1 (soundness)
                // -----------------------------------------------------------------
                // Check 1:  (a - b) * 1 = 0
                //                 a - b = 0
                // => As a != b, the witness is incorrect.
                //
                // Remark: While the multiplier = 1 here, letting multiplier = n,
                //         for n as any field element (n != 0), also holds.
                //
                //
                // Case 4a: a != b AND witness == 1 AND multiplier = n [!= (a - b)^(-1)] (soundness)
                // ---------------------------------------------------------------------------------
                // Check 1:  (a - b) * n = 1
                // => As n != (a - b)^(-1), the witness is incorrect.
                //
                //
                // Case 4b: a != b AND witness == 1 AND multiplier = (a - b)^(-1) (completeness)
                // ---------------------------------------------------------------------------------
                // Check 1:  (a - b) * (a - b)^(-1) = 1
                //                                1 = 1
                // => The witness is trivially correct.
                //
                // Check 2:  (a - b) * not(1) = 0
                //                          0 = 0
                // => The witness is trivially correct.
                //
                cb.borrow_mut().enforce(
                    || function_name!(),
                    |lc| (&a.variable - &b.variable) + lc,
                    |lc| multiplier_variable + lc,
                    |lc| witness_variable + lc,
                );
                cb.borrow_mut().enforce(
                    || function_name!(),
                    |lc| (&a.variable - &b.variable) + lc,
                    |lc| witness_not_variable + lc,
                    |lc| lc,
                );
                Ok(witness.not())
            }
        }
    }
}

#[cfg(test)]
mod constant {
    use super::*;

    #[test]
    fn test_0_equals_0() -> anyhow::Result<()> {
        let candidate = CandidateField::zero().eq(&CandidateField::zero())?;
        assert!(candidate.to_value()?);

        Ok(())
    }

    #[test]
    fn test_1_equals_1() -> anyhow::Result<()> {
        let candidate = CandidateField::one().eq(&CandidateField::one())?;
        assert!(candidate.to_value()?);

        Ok(())
    }

    #[test]
    fn test_0_equals_1() -> anyhow::Result<()> {
        let candidate = CandidateField::zero().eq(&CandidateField::one())?;
        assert!(!candidate.to_value()?);

        Ok(())
    }

    #[test]
    fn test_1_equals_0() -> anyhow::Result<()> {
        let candidate = CandidateField::one().eq(&CandidateField::zero())?;
        assert!(!candidate.to_value()?);

        Ok(())
    }
}

#[cfg(test)]
mod variable {
    use super::*;

    #[test]
    #[named]
    fn test_0_equals_0() -> anyhow::Result<()> {
        let zero = Fr::zero();
        let cb = TestCircuitBuilder(Rc::new(RefCell::new(crate::cs::TestConstraintSystem::<Fr>::new())));

        let public = CandidateField::alloc_public(function_name!(), (zero, cb.clone()))?;
        let private = CandidateField::alloc_private(function_name!(), (zero, cb.clone()))?;

        let candidate = public.eq(&public)?;
        assert!(candidate.to_value()?);

        let candidate = public.eq(&private)?;
        assert!(candidate.to_value()?);

        let candidate = private.eq(&public)?;
        assert!(candidate.to_value()?);

        let candidate = private.eq(&private)?;
        assert!(candidate.to_value()?);

        Ok(())
    }
}
