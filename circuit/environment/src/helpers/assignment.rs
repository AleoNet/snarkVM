// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::Index;
use snarkvm_fields::PrimeField;

use indexmap::IndexMap;

#[derive(Clone, PartialEq, Eq, Hash)]
enum AssignmentVariable<F: PrimeField> {
    Constant(F),
    Public(Index),
    Private(Index),
}

impl<F: PrimeField> From<&crate::Variable<F>> for AssignmentVariable<F> {
    /// Converts a variable to an assignment variable.
    fn from(variable: &crate::Variable<F>) -> Self {
        match variable {
            crate::Variable::Constant(value) => Self::Constant(**value),
            crate::Variable::Public(index, _) => Self::Public(*index),
            crate::Variable::Private(index, _) => Self::Private(*index),
        }
    }
}

#[derive(Clone)]
struct AssignmentLC<F: PrimeField> {
    constant: F,
    terms: IndexMap<AssignmentVariable<F>, F>,
}

impl<F: PrimeField> From<&crate::LinearCombination<F>> for AssignmentLC<F> {
    /// Converts a linear combination to an assignment linear combination.
    fn from(lc: &crate::LinearCombination<F>) -> Self {
        Self {
            constant: lc.to_constant(),
            terms: FromIterator::from_iter(
                lc.to_terms().iter().map(|(variable, coefficient)| (variable.into(), *coefficient)),
            ),
        }
    }
}

/// A struct that contains public variable assignments, private variable assignments,
/// and constraint assignments.
#[derive(Clone)]
pub struct Assignment<F: PrimeField> {
    public: IndexMap<Index, F>,
    private: IndexMap<Index, F>,
    constraints: Vec<(AssignmentLC<F>, AssignmentLC<F>, AssignmentLC<F>)>,
}

impl<F: PrimeField> From<crate::R1CS<F>> for Assignment<F> {
    /// Converts an R1CS to an assignment.
    fn from(r1cs: crate::R1CS<F>) -> Self {
        Self {
            public: FromIterator::from_iter(
                r1cs.to_public_variables().iter().map(|variable| (variable.index(), variable.value())),
            ),
            private: FromIterator::from_iter(
                r1cs.to_private_variables().iter().map(|variable| (variable.index(), variable.value())),
            ),
            constraints: FromIterator::from_iter(r1cs.to_constraints().iter().map(|constraint| {
                let (a, b, c) = constraint.to_terms();
                (a.into(), b.into(), c.into())
            })),
        }
    }
}

impl<F: PrimeField> Assignment<F> {
    /// Returns the public inputs of the assignment.
    pub fn public_inputs(&self) -> Vec<F> {
        self.public.values().cloned().collect()
    }

    /// Returns the number of public variables in the assignment.
    pub fn num_public(&self) -> u64 {
        self.public.len() as u64
    }

    /// Returns the number of private variables in the assignment.
    pub fn num_private(&self) -> u64 {
        self.private.len() as u64
    }

    /// Returns the number of constraints in the assignment.
    pub fn num_constraints(&self) -> u64 {
        self.constraints.len() as u64
    }
}

impl<F: PrimeField> snarkvm_r1cs::ConstraintSynthesizer<F> for Assignment<F> {
    /// Synthesizes the constraints from the environment into a `snarkvm_r1cs`-compliant constraint system.
    fn generate_constraints<CS: snarkvm_r1cs::ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
    ) -> Result<(), snarkvm_r1cs::SynthesisError> {
        /// A struct for tracking the mapping of variables from the virtual machine (first) to the gadget constraint system (second).
        struct Converter {
            public: IndexMap<u64, snarkvm_r1cs::Variable>,
            private: IndexMap<u64, snarkvm_r1cs::Variable>,
        }

        let mut converter = Converter { public: Default::default(), private: Default::default() };

        // Ensure the given `cs` is starting off clean.
        assert_eq!(1, cs.num_public_variables());
        assert_eq!(0, cs.num_private_variables());
        assert_eq!(0, cs.num_constraints());

        // Allocate the public variables.
        for (i, (index, value)) in self.public.iter().enumerate() {
            assert_eq!(i as u64, *index, "Public variables in first system must be processed in lexicographic order");

            let gadget = cs.alloc_input(|| format!("Public {i}"), || Ok(*value))?;

            assert_eq!(
                snarkvm_r1cs::Index::Public((index + 1) as usize),
                gadget.get_unchecked(),
                "Public variables in the second system must match the first system (with an off-by-1 for the public case)"
            );

            let result = converter.public.insert(*index, gadget);

            assert!(result.is_none(), "Overwrote an existing public variable in the converter");
        }

        // Allocate the private variables.
        for (i, (index, value)) in self.private.iter().enumerate() {
            assert_eq!(i as u64, *index, "Private variables in first system must be processed in lexicographic order");

            let gadget = cs.alloc(|| format!("Private {i}"), || Ok(*value))?;

            assert_eq!(
                snarkvm_r1cs::Index::Private(i),
                gadget.get_unchecked(),
                "Private variables in the second system must match the first system"
            );

            let result = converter.private.insert(*index, gadget);

            assert!(result.is_none(), "Overwrote an existing private variable in the converter");
        }

        // Enforce all of the constraints.
        for (i, (a, b, c)) in self.constraints.iter().enumerate() {
            // Converts terms from one linear combination in the first system to the second system.
            let convert_linear_combination = |lc: &AssignmentLC<F>| -> snarkvm_r1cs::LinearCombination<F> {
                // Initialize a linear combination for the second system.
                let mut linear_combination = snarkvm_r1cs::LinearCombination::<F>::zero();

                // Process every term in the linear combination.
                for (variable, coefficient) in lc.terms.iter() {
                    match variable {
                        AssignmentVariable::Constant(_) => {
                            unreachable!(
                                "Failed during constraint translation. The first system by definition cannot have constant variables in the terms"
                            )
                        }
                        AssignmentVariable::Public(index) => {
                            let gadget = converter.public.get(index).unwrap();
                            assert_eq!(
                                snarkvm_r1cs::Index::Public((index + 1) as usize),
                                gadget.get_unchecked(),
                                "Failed during constraint translation. The public variable in the second system must match the first system (with an off-by-1 for the public case)"
                            );
                            linear_combination += (*coefficient, *gadget);
                        }
                        AssignmentVariable::Private(index) => {
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
                linear_combination +=
                    (lc.constant, snarkvm_r1cs::Variable::new_unchecked(snarkvm_r1cs::Index::Public(0)));

                // Return the linear combination of the second system.
                linear_combination
            };

            cs.enforce(
                || format!("Constraint {i}"),
                |lc| lc + convert_linear_combination(a),
                |lc| lc + convert_linear_combination(b),
                |lc| lc + convert_linear_combination(c),
            );
        }

        // Ensure the given `cs` matches in size with the first system.
        assert_eq!(self.num_public() + 1, cs.num_public_variables() as u64);
        assert_eq!(self.num_private(), cs.num_private_variables() as u64);
        assert_eq!(self.num_constraints(), cs.num_constraints() as u64);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use snarkvm_algorithms::{AlgebraicSponge, SNARK};
    use snarkvm_circuit::prelude::*;
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_r1cs::ConstraintSynthesizer;

    /// Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    fn create_example_circuit<E: Environment>() -> Field<E> {
        let one = snarkvm_console_types::Field::<E::Network>::one();
        let two = one + one;

        const EXPONENT: u64 = 64;

        // Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
        let mut candidate = Field::<E>::new(Mode::Public, one);
        let mut accumulator = Field::new(Mode::Private, two);
        for _ in 0..EXPONENT {
            candidate += &accumulator;
            accumulator *= Field::new(Mode::Private, two);
        }

        assert_eq!((accumulator - Field::one()).eject_value(), candidate.eject_value());
        assert_eq!(2, E::num_public());
        assert_eq!(2 * EXPONENT + 1, E::num_private());
        assert_eq!(EXPONENT, E::num_constraints());
        assert!(E::is_satisfied());

        candidate
    }

    #[test]
    fn test_constraint_converter() {
        let _candidate_output = create_example_circuit::<Circuit>();
        let assignment = Circuit::eject_assignment_and_reset();
        assert_eq!(0, Circuit::num_constants());
        assert_eq!(1, Circuit::num_public());
        assert_eq!(0, Circuit::num_private());
        assert_eq!(0, Circuit::num_constraints());

        let mut cs = snarkvm_r1cs::TestConstraintSystem::new();
        assignment.generate_constraints(&mut cs).unwrap();
        {
            use snarkvm_r1cs::ConstraintSystem;
            assert_eq!(assignment.num_public() + 1, cs.num_public_variables() as u64);
            assert_eq!(assignment.num_private(), cs.num_private_variables() as u64);
            assert_eq!(assignment.num_constraints(), cs.num_constraints() as u64);
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_marlin() {
        let _candidate_output = create_example_circuit::<Circuit>();
        let assignment = Circuit::eject_assignment_and_reset();
        assert_eq!(0, Circuit::num_constants());
        assert_eq!(1, Circuit::num_public());
        assert_eq!(0, Circuit::num_private());
        assert_eq!(0, Circuit::num_constraints());

        // Marlin setup, prove, and verify.

        use snarkvm_algorithms::{
            crypto_hash::PoseidonSponge,
            snark::marlin::{ahp::AHPForR1CS, MarlinHidingMode, MarlinSNARK},
        };
        use snarkvm_curves::bls12_377::{Bls12_377, Fq};
        use snarkvm_utilities::rand::TestRng;

        type FS = PoseidonSponge<Fq, 2, 1>;
        type MarlinInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode>;

        let rng = &mut TestRng::default();

        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(200, 200, 300).unwrap();
        let universal_srs = MarlinInst::universal_setup(&max_degree).unwrap();
        let fs_pp = FS::sample_parameters();

        let (index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &assignment).unwrap();
        println!("Called circuit setup");

        let proof = MarlinInst::prove(&fs_pp, &index_pk, &assignment, rng).unwrap();
        println!("Called prover");

        let one = <Circuit as Environment>::BaseField::one();
        assert!(MarlinInst::verify(&fs_pp, &index_vk, [one, one], &proof).unwrap());
        println!("Called verifier");
        println!("\nShould not verify (i.e. verifier messages should print below):");
        assert!(!MarlinInst::verify(&fs_pp, &index_vk, [one, one + one], &proof).unwrap());
    }
}
