// Copyright (C) 2019-2022 Aleo Systems Inc.
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

use snarkvm_circuits_types::Boolean;

#[derive(Debug, Clone)]
pub struct Ciphertext<A: Aleo> {
    commitment: Field<A>,
    randomizer: Field<A>,
    record_view_key_commitment: Field<A>,
    record_elements: Vec<Field<A>>,
    program_id: Field<A>,
    is_dummy: Boolean<A>,
}

impl<A: Aleo> Inject for Ciphertext<A> {
    type Primitive = (A::BaseField, A::BaseField, A::BaseField, Vec<A::BaseField>, A::BaseField, bool);

    /// Initializes an account compute key from the given mode and `(commitment, randomizer, record_view_key_commitment, record_elements, program_id, is_dummy)`.
    fn new(
        mode: Mode,
        (commitment, randomizer, record_view_key_commitment, record_elements, program_id, is_dummy): Self::Primitive,
    ) -> Self {
        Self {
            commitment: Field::new(mode, commitment),
            randomizer: Field::new(mode, randomizer),
            record_view_key_commitment: Field::new(mode, record_view_key_commitment),
            record_elements: record_elements.into_iter().map(|element| Field::new(mode, element)).collect(),
            program_id: Field::new(mode, program_id),
            is_dummy: Boolean::new(mode, is_dummy),
        }
    }
}

impl<A: Aleo> Ciphertext<A> {
    /// Returns the commitment.
    pub fn commitment(&self) -> &Field<A> {
        &self.commitment
    }

    /// Returns the ciphertext randomizer.
    pub fn randomizer(&self) -> &Field<A> {
        &self.randomizer
    }

    /// Returns the record view key commitment.
    pub fn record_view_key_commitment(&self) -> &Field<A> {
        &self.record_view_key_commitment
    }

    /// Returns the record view key commitment.
    pub fn record_elements(&self) -> &Vec<Field<A>> {
        &self.record_elements
    }

    /// Returns the program id.
    pub fn program_id(&self) -> &Field<A> {
        &self.program_id
    }

    /// Returns the is dummy flag.
    pub fn is_dummy(&self) -> &Boolean<A> {
        &self.is_dummy
    }
}

impl<A: Aleo> Eject for Ciphertext<A> {
    type Primitive = (A::BaseField, A::BaseField, A::BaseField, Vec<A::BaseField>, A::BaseField, bool);

    ///
    /// Ejects the mode of the ciphertext.
    ///
    fn eject_mode(&self) -> Mode {
        (
            &self.commitment,
            &self.randomizer,
            &self.record_view_key_commitment,
            &self.record_elements,
            &self.program_id,
            &self.is_dummy,
        )
            .eject_mode()
    }

    ///
    /// Ejects the compute key as `(commitment, randomizer, record_view_key_commitment, record_elements, program_id, is_dummy)`.
    ///
    fn eject_value(&self) -> Self::Primitive {
        (
            &self.commitment,
            &self.randomizer,
            &self.record_view_key_commitment,
            &self.record_elements,
            &self.program_id,
            &self.is_dummy,
        )
            .eject_value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Devnet as Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 1000;

    fn check_new(mode: Mode, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        let rng = &mut test_rng();

        for _ in 0..ITERATIONS {
            let commitment = UniformRand::rand(rng);
            let randomizer = UniformRand::rand(rng);
            let record_view_key_commitment = UniformRand::rand(rng);
            let record_elements = vec![UniformRand::rand(rng)];
            let program_id = UniformRand::rand(rng);
            let is_dummy = UniformRand::rand(rng);

            Circuit::scope(format!("New {mode}"), || {
                let candidate = Ciphertext::<Circuit>::new(
                    mode,
                    (commitment, randomizer, record_view_key_commitment, record_elements.clone(), program_id, is_dummy),
                );
                assert_eq!(mode, candidate.eject_mode());
                assert_eq!(
                    (commitment, randomizer, record_view_key_commitment, record_elements, program_id, is_dummy),
                    candidate.eject_value()
                );
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_ciphertext_new() {
        check_new(Mode::Constant, 6, 0, 0, 0);
        check_new(Mode::Public, 0, 6, 0, 1);
        check_new(Mode::Private, 0, 0, 6, 1);
    }
}
