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

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::Field;
use snarkvm_fields::PoseidonDefaultField;

const RATE: usize = 4;
const OPTIMIZED_FOR_WEIGHTS: bool = false;
const CAPACITY: usize = 1;

/// The mode structure for duplex sponges
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum DuplexSpongeMode {
    /// The sponge is currently absorbing data.
    Absorbing {
        /// next position of the state to be XOR-ed when absorbing.
        next_absorb_index: usize,
    },
    /// The sponge is currently squeezing data out.
    Squeezing {
        /// next position of the state to be outputted when squeezing.
        next_squeeze_index: usize,
    },
}

pub struct Poseidon<E: Environment> {
    /// The number of rounds in a full-round operation.
    full_rounds: usize,
    /// The number of rounds in a partial-round operation.
    partial_rounds: usize,
    /// The exponent used in S-boxes.
    alpha: Field<E>,
    /// The additive round keys. These are added before each MDS matrix application to make it an affine shift.
    /// They are indexed by `ark[round_number][state_element_index]`
    ark: Vec<Vec<Field<E>>>,
    /// The Maximally Distance Separating (MDS) matrix.
    mds: Vec<Vec<Field<E>>>,
}

impl<E: Environment> Poseidon<E> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        match E::BaseField::default_poseidon_parameters::<RATE>(OPTIMIZED_FOR_WEIGHTS) {
            Some(parameters) => {
                let full_rounds = parameters.full_rounds;
                let partial_rounds = parameters.partial_rounds;
                let alpha = Field::constant(E::BaseField::from(parameters.alpha as u128));
                let ark = parameters
                    .ark
                    .into_iter()
                    .take(full_rounds + partial_rounds)
                    .map(|round| round.into_iter().take(RATE + 1).map(Field::constant).collect())
                    .collect();
                let mds = parameters
                    .mds
                    .into_iter()
                    .take(RATE + 1)
                    .map(|round| round.into_iter().take(RATE + 1).map(Field::constant).collect())
                    .collect();

                Self { full_rounds, partial_rounds, alpha, ark, mds }
            }
            None => E::halt("Failed to initialize the Poseidon hash function"),
        }
    }

    pub fn hash(&self, input: &[Field<E>]) -> Field<E> {
        let mut state = vec![Field::zero(); RATE + CAPACITY];
        let mut mode = DuplexSpongeMode::Absorbing { next_absorb_index: 0 };

        self.absorb(&mut state, &mut mode, input);
        self.squeeze(&mut state, &mut mode, 1)[0].clone()
    }
}

impl<E: Environment> Poseidon<E> {
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

    #[inline]
    fn absorb_internal(
        &self,
        state: &mut [Field<E>],
        mode: &mut DuplexSpongeMode,
        mut absorb_index: usize,
        input: &[Field<E>],
    ) {
        if !input.is_empty() {
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

    #[inline]
    fn squeeze_internal(
        &self,
        state: &mut [Field<E>],
        mode: &mut DuplexSpongeMode,
        mut squeeze_index: usize,
        output: &mut [Field<E>],
    ) {
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

    #[inline]
    fn absorb(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, input: &[Field<E>]) {
        if !input.is_empty() {
            match mode {
                DuplexSpongeMode::Absorbing { next_absorb_index } => {
                    let mut absorb_index = *next_absorb_index;
                    if absorb_index == RATE {
                        self.permute(state);
                        absorb_index = 0;
                    }
                    self.absorb_internal(state, mode, absorb_index, input);
                }
                DuplexSpongeMode::Squeezing { next_squeeze_index: _ } => {
                    self.permute(state);
                    self.absorb_internal(state, mode, 0, input);
                }
            }
        }
    }

    #[inline]
    fn squeeze(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, num_outputs: usize) -> Vec<Field<E>> {
        let mut output = vec![Field::zero(); num_outputs];
        if num_outputs != 0 {
            match mode {
                DuplexSpongeMode::Absorbing { next_absorb_index: _ } => {
                    self.permute(state);
                    self.squeeze_internal(state, mode, 0, &mut output);
                }
                DuplexSpongeMode::Squeezing { next_squeeze_index } => {
                    let mut squeeze_index = *next_squeeze_index;
                    if squeeze_index == RATE {
                        self.permute(state);
                        squeeze_index = 0;
                    }
                    self.squeeze_internal(state, mode, squeeze_index, &mut output);
                }
            }
        }
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::crypto_hash::Poseidon as NativePoseidon;
    use snarkvm_circuits_environment::{assert_scope, Circuit};
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: usize = 1;

    fn check_hash<const NUM_INPUTS: usize>(
        mode: Mode,
        num_constants: usize,
        num_public: usize,
        num_private: usize,
        num_constraints: usize,
    ) {
        let mut rng = test_rng();

        let native = NativePoseidon::<_, RATE, OPTIMIZED_FOR_WEIGHTS>::setup();
        let circuit = Poseidon::new();

        for i in 0..ITERATIONS {
            // Compute the native hash.
            let input =
                (0..NUM_INPUTS).map(|_| <Circuit as Environment>::BaseField::rand(&mut rng)).collect::<Vec<_>>();
            let expected = native.evaluate(&input);

            // Prepare the circuit preimage.
            let preimage = input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i}"), || {
                let candidate = circuit.hash(&preimage);
                assert_eq!(expected, candidate.eject_value());
                // assert!(Circuit::is_satisfied());
                assert_scope!(num_constants, num_public, num_private, num_constraints);
            });
        }
    }

    #[test]
    fn test_poseidon() {
        check_hash::<5>(Mode::Constant, 253, 0, 0, 0);
        check_hash::<5>(Mode::Public, 253, 0, 705, 705);
        check_hash::<5>(Mode::Private, 253, 0, 705, 705);
    }
}
