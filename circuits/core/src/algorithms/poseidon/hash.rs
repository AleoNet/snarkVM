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
use crate::Hash;

impl<E: Environment> Hash for Poseidon<E> {
    type Input = Field<E>;
    type Output = Field<E>;

    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        // Initialize a new sponge.
        let mut state = vec![Field::zero(); RATE + CAPACITY];
        let mut mode = DuplexSpongeMode::Absorbing { next_absorb_index: 0 };

        // Absorb the input and squeeze the output.
        self.absorb(&mut state, &mut mode, input);
        self.squeeze(&mut state, &mut mode, 1)[0].clone()
    }
}

impl<E: Environment> Count<dyn Hash<Input = Field<E>, Output = Field<E>>> for Poseidon<E> {
    type Case = ();

    fn count(_parameter: &Self::Case) -> CircuitCount {
        todo!()
    }
}

impl<E: Environment> OutputMode<dyn Hash<Input = Field<E>, Output = Field<E>>> for Poseidon<E> {
    type Case = ();

    fn output_mode(_parameter: &Self::Case) -> Mode {
        todo!()
    }
}

impl<E: Environment> Poseidon<E> {
    /// Absorbs the input elements into state.
    #[inline]
    pub(super) fn absorb(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, input: &[Field<E>]) {
        if !input.is_empty() {
            // Determine the absorb index.
            let (mut absorb_index, should_permute) = match *mode {
                DuplexSpongeMode::Absorbing { next_absorb_index } => match next_absorb_index == RATE {
                    true => (0, true),
                    false => (next_absorb_index, false),
                },
                DuplexSpongeMode::Squeezing { .. } => (0, true),
            };

            // Proceed to permute the state, if necessary.
            if should_permute {
                self.permute(state);
            }

            let mut remaining = input;
            loop {
                // Compute the starting index.
                let start = CAPACITY + absorb_index;

                // Check if we can exit the loop.
                if absorb_index + remaining.len() <= RATE {
                    // Absorb the state elements into the input.
                    remaining.iter().enumerate().for_each(|(i, element)| state[start + i] += element);
                    // Update the sponge mode.
                    *mode = DuplexSpongeMode::Absorbing { next_absorb_index: absorb_index + remaining.len() };
                    return;
                }

                // Otherwise, proceed to absorb `(rate - absorb_index)` elements.
                let num_absorbed = RATE - absorb_index;
                remaining.iter().enumerate().take(num_absorbed).for_each(|(i, element)| state[start + i] += element);

                // Permute the state.
                self.permute(state);

                // Repeat with the updated input slice and absorb index.
                remaining = &remaining[num_absorbed..];
                absorb_index = 0;
            }
        }
    }

    /// Squeeze the specified number of state elements into the output.
    #[inline]
    pub(super) fn squeeze(
        &self,
        state: &mut [Field<E>],
        mode: &mut DuplexSpongeMode,
        num_outputs: usize,
    ) -> Vec<Field<E>> {
        let mut output = vec![Field::zero(); num_outputs];
        if num_outputs != 0 {
            self.squeeze_internal(state, mode, &mut output);
        }
        output
    }

    /// Squeeze the state elements into the output.
    #[inline]
    fn squeeze_internal(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, output: &mut [Field<E>]) {
        // Determine the squeeze index.
        let (mut squeeze_index, should_permute) = match *mode {
            DuplexSpongeMode::Absorbing { .. } => (0, true),
            DuplexSpongeMode::Squeezing { next_squeeze_index } => match next_squeeze_index == RATE {
                true => (0, true),
                false => (next_squeeze_index, false),
            },
        };

        // Proceed to permute the state, if necessary.
        if should_permute {
            self.permute(state);
        }

        let mut remaining = output;
        loop {
            // Compute the starting index.
            let start = CAPACITY + squeeze_index;

            // Check if we can exit the loop.
            if squeeze_index + remaining.len() <= RATE {
                // Store the state elements into the output.
                remaining.clone_from_slice(&state[start..(start + remaining.len())]);
                // Update the sponge mode.
                *mode = DuplexSpongeMode::Squeezing { next_squeeze_index: squeeze_index + remaining.len() };
                return;
            }

            // Otherwise, proceed to squeeze `(rate - squeeze_index)` elements.
            let num_squeezed = RATE - squeeze_index;
            remaining[..num_squeezed].clone_from_slice(&state[start..(start + num_squeezed)]);

            // Unless we are done with squeezing in this call, permute.
            if remaining.len() != RATE {
                self.permute(state);
            }
            // Repeat with the updated output slice and squeeze index.
            remaining = &mut remaining[num_squeezed..];
            squeeze_index = 0;
        }
    }

    /// Apply the additive round keys in-place.
    #[inline]
    fn apply_ark(&self, state: &mut [Field<E>], round: usize) {
        for (i, element) in state.iter_mut().enumerate() {
            *element += &self.ark[round][i];
        }
    }

    /// Apply the S-Box based on whether it is a full round or partial round.
    #[inline]
    fn apply_s_box(&self, state: &mut [Field<E>], is_full_round: bool) {
        if is_full_round {
            // Full rounds apply the S Box (x^alpha) to every element of state
            for element in state.iter_mut() {
                *element = (&*element).pow(&self.alpha);
            }
        } else {
            // Partial rounds apply the S Box (x^alpha) to just the first element of state
            state[0] = (&state[0]).pow(&self.alpha);
        }
    }

    /// Apply the Maximally Distance Separating (MDS) matrix in-place.
    #[inline]
    fn apply_mds(&self, state: &mut [Field<E>]) {
        let mut new_state = Vec::with_capacity(state.len());
        for i in 0..state.len() {
            let mut accumulator = Field::zero();
            for (j, element) in state.iter().enumerate() {
                accumulator += element * &self.mds[i][j];
            }
            new_state.push(accumulator);
        }
        state.clone_from_slice(&new_state[..state.len()]);
    }

    /// Apply the permutation for all rounds in-place.
    #[inline]
    fn permute(&self, state: &mut [Field<E>]) {
        // Determine the partial rounds range bound.
        let partial_rounds = self.partial_rounds;
        let full_rounds = self.full_rounds;
        let full_rounds_over_2 = full_rounds / 2;
        let partial_round_range = full_rounds_over_2..(full_rounds_over_2 + partial_rounds);

        // Iterate through all rounds to permute.
        for i in 0..(partial_rounds + full_rounds) {
            let is_full_round = !partial_round_range.contains(&i);
            self.apply_ark(state, i);
            self.apply_s_box(state, is_full_round);
            self.apply_mds(state);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::crypto_hash::Poseidon as NativePoseidon;
    use snarkvm_circuits_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 10;

    fn check_hash(
        mode: Mode,
        num_inputs: usize,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let rng = &mut test_rng();
        let native_poseidon = NativePoseidon::<_, RATE, OPTIMIZED_FOR_WEIGHTS>::setup();
        let poseidon = Poseidon::new();

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let native_input =
                (0..num_inputs).map(|_| <Circuit as Environment>::BaseField::rand(rng)).collect::<Vec<_>>();
            let input = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            let expected = native_poseidon.evaluate(&native_input);
            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i}"), || {
                let candidate = poseidon.hash(&input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_hash_constant() {
        for num_inputs in 0..=RATE {
            check_hash(Mode::Constant, num_inputs, 0, 0, 0, 0);
        }
    }

    #[test]
    fn test_hash_public() {
        check_hash(Mode::Public, 0, 0, 0, 0, 0);
        check_hash(Mode::Public, 1, 0, 0, 335, 335);
        check_hash(Mode::Public, 2, 0, 0, 340, 340);
        check_hash(Mode::Public, 3, 0, 0, 345, 345);
        check_hash(Mode::Public, 4, 0, 0, 350, 350);
        check_hash(Mode::Public, 5, 0, 0, 705, 705);
        check_hash(Mode::Public, 6, 0, 0, 705, 705);
        check_hash(Mode::Public, 7, 0, 0, 705, 705);
        check_hash(Mode::Public, 8, 0, 0, 705, 705);
        check_hash(Mode::Public, 9, 0, 0, 1060, 1060);
        check_hash(Mode::Public, 10, 0, 0, 1060, 1060);
    }

    #[test]
    fn test_hash_private() {
        check_hash(Mode::Private, 0, 0, 0, 0, 0);
        check_hash(Mode::Private, 1, 0, 0, 335, 335);
        check_hash(Mode::Private, 2, 0, 0, 340, 340);
        check_hash(Mode::Private, 3, 0, 0, 345, 345);
        check_hash(Mode::Private, 4, 0, 0, 350, 350);
        check_hash(Mode::Private, 5, 0, 0, 705, 705);
        check_hash(Mode::Private, 6, 0, 0, 705, 705);
        check_hash(Mode::Private, 7, 0, 0, 705, 705);
        check_hash(Mode::Private, 8, 0, 0, 705, 705);
        check_hash(Mode::Private, 9, 0, 0, 1060, 1060);
        check_hash(Mode::Private, 10, 0, 0, 1060, 1060);
    }
}
