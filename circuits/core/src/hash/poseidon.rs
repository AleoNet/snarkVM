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
    #[inline]
    fn apply_ark(&self, state: &mut [Field<E>], round: usize) {
        // Adds ark in place.
        for (i, element) in state.iter_mut().enumerate() {
            *element += &self.ark[round][i];
        }
    }

    #[inline]
    fn apply_s_box(&self, state: &mut [Field<E>], is_full_round: bool) {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for element in state.iter_mut() {
                *element = (&*element).pow(&self.alpha);
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the first element of state
        else {
            state[0] = (&state[0]).pow(&self.alpha);
        }
    }

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
        mut rate_start_index: usize,
        input: &[Field<E>],
    ) {
        if !input.is_empty() {
            let mut remaining_elements = input;

            let mut loop_counter = 0;
            loop {
                // if we can finish in this call
                if rate_start_index + remaining_elements.len() <= RATE {
                    for (i, element) in remaining_elements.iter().enumerate() {
                        // Absorb
                        state[CAPACITY + i + rate_start_index] += element;
                    }
                    *mode =
                        DuplexSpongeMode::Absorbing { next_absorb_index: rate_start_index + remaining_elements.len() };

                    return;
                }
                // otherwise absorb (rate - rate_start_index) elements
                let num_elements_absorbed = RATE - rate_start_index;
                for (i, element) in remaining_elements.iter().enumerate().take(num_elements_absorbed) {
                    // Absorb
                    state[CAPACITY + i + rate_start_index] += element;
                }
                self.permute(state);
                // the input elements got truncated by num elements absorbed
                remaining_elements = &remaining_elements[num_elements_absorbed..];
                rate_start_index = 0;

                loop_counter += 1;
            }
        }
    }

    #[inline]
    fn squeeze_internal(
        &self,
        state: &mut [Field<E>],
        mode: &mut DuplexSpongeMode,
        mut rate_start_index: usize,
        output: &mut [Field<E>],
    ) {
        let mut remaining_output = output;

        let mut loop_counter = 0;
        loop {
            // if we can finish in this call
            if rate_start_index + remaining_output.len() <= RATE {
                remaining_output.clone_from_slice(
                    &state[CAPACITY + rate_start_index..(CAPACITY + remaining_output.len() + rate_start_index)],
                );
                *mode = DuplexSpongeMode::Squeezing { next_squeeze_index: rate_start_index + remaining_output.len() };
                return;
            }
            // otherwise squeeze (rate - rate_start_index) elements
            let num_squeezed = RATE - rate_start_index;
            remaining_output[..num_squeezed]
                .clone_from_slice(&state[CAPACITY + rate_start_index..(CAPACITY + num_squeezed + rate_start_index)]);

            // Unless we are done with squeezing in this call, permute.
            if remaining_output.len() != RATE {
                self.permute(state);
            }
            // Repeat with updated output slices and rate start index
            remaining_output = &mut remaining_output[num_squeezed..];
            rate_start_index = 0;

            loop_counter += 1;
        }
    }

    #[inline]
    fn absorb(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, input: &[Field<E>]) {
        if !input.is_empty() {
            match mode {
                DuplexSpongeMode::Absorbing { next_absorb_index } => {
                    // Absorb permute.
                    let mut absorb_index = *next_absorb_index;
                    if absorb_index == RATE {
                        self.permute(state);
                        absorb_index = 0;
                    }
                    self.absorb_internal(state, mode, absorb_index, &input);
                }
                DuplexSpongeMode::Squeezing { next_squeeze_index: _ } => {
                    // Squeeze permute.
                    self.permute(state);
                    self.absorb_internal(state, mode, 0, &input);
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
                    // Absorb permute.
                    self.permute(state);
                    self.squeeze_internal(state, mode, 0, &mut output);
                }
                DuplexSpongeMode::Squeezing { next_squeeze_index } => {
                    // Squeeze permute.
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
    use snarkvm_algorithms::{crypto_hash::PoseidonSponge, AlgebraicSponge};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::sync::Arc;

    #[test]
    fn test_poseidon() {
        let mut rng = test_rng();
        let parameters =
            <Circuit as Environment>::BaseField::default_poseidon_parameters::<RATE>(OPTIMIZED_FOR_WEIGHTS).unwrap();

        let mode = Mode::Private;

        let native_input: Vec<_> = (0..256).map(|_| <Circuit as Environment>::BaseField::rand(&mut rng)).collect();
        let candidate_input: Vec<_> = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect();

        let expected = {
            let mut native_poseidon = PoseidonSponge::new(&Arc::new(parameters));
            native_poseidon.absorb(&native_input);
            native_poseidon.squeeze(1)[0]
        };

        let candidate = Poseidon::new().hash(&candidate_input);
        assert_eq!(expected, candidate.eject_value());
        assert!(Circuit::is_satisfied());
    }
}
