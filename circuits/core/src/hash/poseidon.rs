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

use snarkvm_algorithms::{crypto_hash::PoseidonCryptoHash, CryptoHash};
use snarkvm_circuits_environment::{traits::*, Environment};
use snarkvm_circuits_types::{Boolean, Field, I64};

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

pub struct Poseidon<E: Environment>(PoseidonCryptoHash<E::BaseField, RATE, OPTIMIZED_FOR_WEIGHTS>);

impl<E: Environment> Poseidon<E> {
    fn new() -> Self {
        Self(PoseidonCryptoHash::<E::BaseField, RATE, OPTIMIZED_FOR_WEIGHTS>::setup())
    }

    fn hash(&self, input: &[Field<E>]) -> Field<E> {
        let mut state = [Field::zero(); RATE + CAPACITY];
        let mut mode = DuplexSpongeMode::Absorbing { next_absorb_index: 0 };

        self.absorb(&mut state, &mut mode, input);
        self.squeeze(&mut state, &mut mode, 1)[0].clone()
    }
}

impl<E: Environment> Poseidon<E> {
    fn apply_ark(&self, state: &mut [Field<E>], round_number: usize) {
        // Adds ark in place.
        for (i, element) in state.iter_mut().enumerate() {
            element.add_constant_in_place(&self.0.parameters.ark[round_number][i])?;
        }
    }

    fn apply_s_box(&self, state: &mut [Field<E>], is_full_round: bool) {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for (i, state_item) in state.iter_mut().enumerate() {
                *state_item = state_item.pow_by_constant(&[self.parameters.alpha])?;
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the first element of state
        else {
            state[0] = state[0].pow_by_constant(&[self.parameters.alpha])?;
        }
    }

    fn apply_mds(&self, state: &mut [Field<E>]) {
        let mut new_state = Vec::new();
        for i in 0..state.len() {
            let mut cur = Field::zero();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem.mul_by_constant(&self.parameters.mds[i][j])?;
                cur.add_in_place(&term)?;
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()]);
    }

    fn permute(&self, state: &mut [Field<E>]) {
        let partial_rounds = self.0.parameters.partial_rounds;
        let full_rounds = self.0.parameters.full_rounds;
        let full_rounds_over_2 = full_rounds / 2;

        let mut internal = state.clone();

        for i in 0..full_rounds_over_2 {
            self.apply_ark(&mut internal, i);
            self.apply_s_box(&mut internal, true);
            self.apply_mds(&mut internal);
        }

        for i in full_rounds_over_2..(full_rounds_over_2 + partial_rounds) {
            self.apply_ark(&mut internal, i);
            self.apply_s_box(&mut internal, false);
            self.apply_mds(&mut internal);
        }

        for i in (full_rounds_over_2 + partial_rounds)..(partial_rounds + full_rounds) {
            self.apply_ark(&mut internal, i);
            self.apply_s_box(&mut internal, true);
            self.apply_mds(&mut internal);
        }

        *state = internal;
    }

    fn absorb_internal(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, mut rate_start_index: usize, input: &[Field<E>]) {
        if !input.is_empty() {
            let mut remaining_elements = input;

            let mut loop_counter = 0;
            loop {
                // if we can finish in this call
                if rate_start_index + remaining_elements.len() <= RATE {
                    for (i, element) in remaining_elements.iter().enumerate() {
                        // Absorb
                        state[CAPACITY + i + rate_start_index].add_in_place(element)?;
                    }
                    *mode = DuplexSpongeMode::Absorbing { next_absorb_index: rate_start_index + remaining_elements.len() };

                    return;
                }
                // otherwise absorb (rate - rate_start_index) elements
                let num_elements_absorbed = RATE - rate_start_index;
                for (i, element) in remaining_elements.iter().enumerate().take(num_elements_absorbed) {
                    // Absorb
                    state[CAPACITY + i + rate_start_index].add_in_place(element)?;
                }
                self.permute(state);
                // the input elements got truncated by num elements absorbed
                remaining_elements = &remaining_elements[num_elements_absorbed..];
                rate_start_index = 0;

                loop_counter += 1;
            }
        }
    }

    fn squeeze_internal(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, mut rate_start_index: usize, output: &mut [Field<E>]) {
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
            remaining_output[..num_squeezed].clone_from_slice(
                &state[CAPACITY + rate_start_index..(CAPACITY + num_squeezed + rate_start_index)],
            );

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

    fn squeeze(&self, state: &mut [Field<E>], mode: &mut DuplexSpongeMode, num_outputs: usize) -> Vec<Field<E>> {
        let mut output = vec![Field::zero(); num_outputs];
        if num_outputs != 0 {
            match mode {
                DuplexSpongeMode::Absorbing { next_absorb_index: _ } => {
                    // Absorb permute.
                    self.permute(state);
                    self.squeeze_internal(state, mode,0, &mut output);
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
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_circuits_types::{Field, Group};

    #[test]
    fn test_record_data() {
        let first = Field::<Circuit>::from_str("10field.public");
        let second = Boolean::from_str("true.private");
        let third = I64::from_str("99i64.public");

        let _candidate = Record {
            owner: Address::from(Group::from_str("2group.private")),
            value: I64::from_str("1i64.private"),
            data: vec![Box::new(first), Box::new(second), Box::new(third)],
        };
    }
}
