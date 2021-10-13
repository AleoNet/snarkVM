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

use crate::models::{ConstraintSystem, LinearCombination, Variable};
use snarkvm_curves::{
    bls12_377::Fr,
    edwards_bls12::{EdwardsAffine, EdwardsParameters},
    AffineCurve,
};
use snarkvm_fields::PrimeField;

use std::collections::HashMap;

/// A struct for tracking the mapping of variables from the virtual machine (first) to the gadget constraint system (second).
struct Converter {
    public: HashMap<u64, snarkvm_r1cs::Variable>,
    private: HashMap<u64, snarkvm_r1cs::Variable>,
}

impl snarkvm_r1cs::ConstraintSynthesizer<Fr> for ConstraintSystem<Fr> {
    fn generate_constraints<CS: snarkvm_r1cs::ConstraintSystem<Fr>>(
        &self,
        mut cs: &mut CS,
    ) -> Result<(), snarkvm_r1cs::SynthesisError> {
        let mut converter = Converter {
            public: Default::default(),
            private: Default::default(),
        };

        // Allocate the public variables.
        for (i, public) in self.to_public_variables().iter().enumerate() {
            match public {
                Variable::Public(index, value) => {
                    assert_eq!(
                        i as u64, *index,
                        "Public variables in first system must be processed in lexicographic order"
                    );

                    let gadget = cs.alloc_input(|| format!("Public {}", i), || Ok(value.clone()))?;

                    assert_eq!(
                        snarkvm_r1cs::Index::Public((index + 1) as usize),
                        gadget.get_unchecked(),
                        "Public variables in the second system must match the first system (with an off-by-1 for the public case)"
                    );

                    let result = converter.public.insert(*index, gadget);

                    assert!(
                        result.is_none(),
                        "Overwrote an existing public variable in the converter"
                    );
                }
                _ => unreachable!("Public variables in the first system are not well-formed"),
            }
        }

        // Allocate the private variables.
        for (i, private) in self.to_private_variables().iter().enumerate() {
            match private {
                Variable::Private(index, value) => {
                    assert_eq!(
                        i as u64, *index,
                        "Private variables in first system must be processed in lexicographic order"
                    );

                    let gadget = cs.alloc(|| format!("Private {}", i), || Ok(value.clone()))?;

                    assert_eq!(
                        snarkvm_r1cs::Index::Private(i),
                        gadget.get_unchecked(),
                        "Private variables in the second system must match the first system"
                    );

                    let result = converter.private.insert(*index, gadget);

                    assert!(
                        result.is_none(),
                        "Overwrote an existing private variable in the converter"
                    );
                }
                _ => unreachable!("Private variables in the first system are not well-formed"),
            }
        }

        // Enforce all of the constraints.
        for (i, (a, b, c)) in self.to_constraints().iter().enumerate() {
            // Converts terms from one linear combination in the first system to the second system.
            let convert_linear_combination = |lc: &LinearCombination<Fr>| -> snarkvm_r1cs::LinearCombination<Fr> {
                // Initialize a linear combination for the second system.
                let mut linear_combination = snarkvm_r1cs::LinearCombination::<Fr>::zero();

                // Keep an accumulator for constant values in the linear combination.
                let mut constant_accumulator = lc.to_constant();
                // Process every term in the linear combination.
                for (variable, coefficient) in lc.to_terms() {
                    match variable {
                        Variable::Constant(value) => {
                            constant_accumulator += value;
                        }
                        Variable::Public(index, _) => {
                            let gadget = converter.public.get(index).unwrap();
                            assert_eq!(
                                snarkvm_r1cs::Index::Public((index + 1) as usize),
                                gadget.get_unchecked(),
                                "Failed during constraint translation. The public variable in the second system must match the first system (with an off-by-1 for the public case)"
                            );
                            linear_combination += (*coefficient, *gadget);
                        }
                        Variable::Private(index, _) => {
                            let gadget = converter.private.get(index).unwrap();
                            assert_eq!(
                                snarkvm_r1cs::Index::Private(*index as usize),
                                gadget.get_unchecked(),
                                "Failed during constraint translation. The private variable in the second system must match the first system"
                            );
                            linear_combination += (*coefficient, *gadget);
                        }
                    }
                }

                // Finally, add the accumulated constant value to the linear combination.
                linear_combination += (
                    constant_accumulator,
                    snarkvm_r1cs::Variable::new_unchecked(snarkvm_r1cs::Index::Public(0)),
                );

                // Return the linear combination of the second system.
                linear_combination
            };

            cs.enforce(
                || format!("Constraint {}", i),
                |lc| lc + convert_linear_combination(a),
                |lc| lc + convert_linear_combination(b),
                |lc| lc + convert_linear_combination(c),
            );
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Circuit, Environment, Field, Mode, One};
    use snarkvm_fields::One as O;
    use snarkvm_r1cs::ConstraintSynthesizer;

    const ITERATIONS: usize = 1000;

    #[test]
    fn test_constraint_converter() {
        let one = <Circuit as Environment>::BaseField::one();
        let two = one + one;

        const EXPONENT: usize = 64;

        // Compute 2^EXPONENT - 1, in a constraint inefficient manner for testing.
        let mut candidate = Field::<Circuit>::new(Mode::Public, one);
        let mut accumulator = Field::<Circuit>::new(Mode::Private, two);
        for i in 0..EXPONENT {
            candidate += &accumulator;
            accumulator *= Field::new(Mode::Private, two);
        }
        assert_eq!((accumulator - Field::one()).to_value(), candidate.to_value());
        assert_eq!(2, Circuit::num_public());
        assert_eq!(2 * EXPONENT + 1, Circuit::num_private());
        assert_eq!(EXPONENT, Circuit::num_constraints());
        assert!(Circuit::is_satisfied());

        let mut cs = snarkvm_r1cs::TestConstraintSystem::new();
        Circuit::cs().circuit.borrow().generate_constraints(&mut cs).unwrap();
        {
            use snarkvm_r1cs::ConstraintSystem;
            assert_eq!(Circuit::num_public() + 1, cs.num_public_variables());
            assert_eq!(Circuit::num_private(), cs.num_private_variables());
            assert_eq!(Circuit::num_constraints(), cs.num_constraints());
            assert!(cs.is_satisfied());
        }
    }
}
