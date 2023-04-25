// Copyright (C) 2019-2023 Aleo Systems Inc.
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

use rand::{CryptoRng, Rng};
use snarkvm_fields::Field;
use snarkvm_r1cs::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

#[doc(hidden)]
#[derive(Clone)]
/// This Circuit is only for testing and should not be used in production
pub struct TestCircuit<F: Field> {
    pub a: Option<F>,
    pub b: Option<F>,
    pub num_constraints: usize,
    pub num_variables: usize,
    pub mul_depth: usize,
}

impl<F: Field> core::fmt::Debug for TestCircuit<F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "TestCircuit {{ num_constraints: {}, num_variables: {}, mul_depth: {} }}",
            self.num_constraints, self.num_variables, self.mul_depth
        )
    }
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for TestCircuit<ConstraintF> {
    fn generate_constraints<CS: ConstraintSystem<ConstraintF>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;

        let mut mul_vars = Vec::with_capacity(self.mul_depth);
        for i in 0..self.mul_depth {
            let mul_var = cs.alloc_input(
                || format!("mul_var {i}"),
                || {
                    let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                    let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                    for _ in 0..(1 + i) {
                        a.mul_assign(&b);
                    }
                    Ok(a)
                },
            )?;
            mul_vars.push(mul_var);
        }

        for i in 0..(self.num_variables - 2 - self.mul_depth) {
            let _ = cs.alloc(|| format!("var {i}"), || self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        let mul_constraints = self.mul_depth - 1;
        for i in 0..(self.num_constraints - mul_constraints) {
            cs.enforce(|| format!("constraint {i}"), |lc| lc + a, |lc| lc + b, |lc| lc + mul_vars[0]);
        }

        for i in 0..mul_constraints {
            cs.enforce(|| format!("constraint_mul {i}"), |lc| lc + mul_vars[i], |lc| lc + b, |lc| lc + mul_vars[i + 1]);
        }

        Ok(())
    }
}

impl<F: Field> TestCircuit<F> {
    pub fn gen_rand<R: Rng + CryptoRng>(
        mul_depth: usize,
        num_constraints: usize,
        num_variables: usize,
        rng: &mut R,
    ) -> (Self, Vec<F>) {
        let mut public_inputs: Vec<F> = Vec::with_capacity(mul_depth);
        let a = F::rand(rng);
        let b = F::rand(rng);

        for j in 1..(mul_depth + 1) {
            let mut new_var = a;
            for _ in 0..j {
                new_var.mul_assign(&b);
            }
            public_inputs.push(new_var);
        }

        (TestCircuit { a: Some(a), b: Some(b), num_constraints, num_variables, mul_depth }, public_inputs)
    }
}
