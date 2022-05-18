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

use crate::{AlgebraicSponge, DefaultCapacityAlgebraicSponge, DuplexSpongeMode};
use snarkvm_fields::{PoseidonParameters, PrimeField};

use smallvec::SmallVec;
use std::{
    ops::{Index, IndexMut},
    sync::Arc,
};

#[derive(Copy, Clone, Debug)]
pub struct State<F: PrimeField, const RATE: usize, const CAPACITY: usize> {
    capacity_state: [F; CAPACITY],
    rate_state: [F; RATE],
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> Default for State<F, RATE, CAPACITY> {
    fn default() -> Self {
        Self { capacity_state: [F::zero(); CAPACITY], rate_state: [F::zero(); RATE] }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> State<F, RATE, CAPACITY> {
    /// Returns an immutable iterator over the state.
    pub fn iter(&self) -> impl Iterator<Item = &F> {
        self.capacity_state.iter().chain(self.rate_state.iter())
    }

    /// Returns an mutable iterator over the state.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut F> {
        self.capacity_state.iter_mut().chain(self.rate_state.iter_mut())
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> Index<usize> for State<F, RATE, CAPACITY> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < RATE + CAPACITY, "Index out of bounds: index is {} but length is {}", index, RATE + CAPACITY);
        if index < CAPACITY { &self.capacity_state[index] } else { &self.rate_state[index - CAPACITY] }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> IndexMut<usize> for State<F, RATE, CAPACITY> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < RATE + CAPACITY, "Index out of bounds: index is {} but length is {}", index, RATE + CAPACITY);
        if index < CAPACITY { &mut self.capacity_state[index] } else { &mut self.rate_state[index - CAPACITY] }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Poseidon<F: PrimeField, const RATE: usize> {
    parameters: Arc<PoseidonParameters<F, RATE, 1>>,
}

impl<F: PrimeField, const RATE: usize> Poseidon<F, RATE> {
    /// Initializes a new instance of the cryptographic hash function.
    pub fn setup() -> Self {
        Self { parameters: Arc::new(F::default_poseidon_parameters::<RATE>().unwrap()) }
    }

    /// Evaluate the cryptographic hash function over a list of field elements as input.
    pub fn evaluate(&self, input: &[F]) -> F {
        self.evaluate_many(input, 1)[0]
    }

    /// Evaluate the cryptographic hash function over a list of field elements as input,
    /// and returns the specified number of field elements as output.
    pub fn evaluate_many(&self, input: &[F], num_outputs: usize) -> Vec<F> {
        let mut sponge = PoseidonSponge::<F, RATE, 1>::new(&self.parameters);
        sponge.absorb(input);
        sponge.squeeze(num_outputs).to_vec()
    }

    /// Evaluate the cryptographic hash function over a non-fixed-length vector,
    /// in which the length also needs to be hashed.
    pub fn evaluate_with_len(&self, input: &[F]) -> F {
        self.evaluate(&[vec![F::from(input.len() as u128)], input.to_vec()].concat())
    }

    pub fn parameters(&self) -> &Arc<PoseidonParameters<F, RATE, 1>> {
        &self.parameters
    }
}

/// A duplex sponge based using the Poseidon permutation.
///
/// This implementation of Poseidon is entirely from Fractal's implementation in [COS20][cos]
/// with small syntax changes.
///
/// [cos]: https://eprint.iacr.org/2019/1076
#[derive(Clone, Debug)]
pub struct PoseidonSponge<F: PrimeField, const RATE: usize, const CAPACITY: usize> {
    /// Sponge Parameters
    parameters: Arc<PoseidonParameters<F, RATE, CAPACITY>>,
    /// Current sponge's state (current elements in the permutation block)
    state: State<F, RATE, CAPACITY>,
    /// Current mode (whether its absorbing or squeezing)
    pub mode: DuplexSpongeMode,
}

impl<F: PrimeField, const RATE: usize> DefaultCapacityAlgebraicSponge<F, RATE> for PoseidonSponge<F, RATE, 1> {
    fn sample_parameters() -> Arc<PoseidonParameters<F, RATE, 1>> {
        Arc::new(F::default_poseidon_parameters::<RATE>().unwrap())
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> AlgebraicSponge<F, RATE, CAPACITY>
    for PoseidonSponge<F, RATE, CAPACITY>
{
    type Parameters = Arc<PoseidonParameters<F, RATE, CAPACITY>>;

    fn new(parameters: &Self::Parameters) -> Self {
        Self {
            parameters: parameters.clone(),
            state: State::default(),
            mode: DuplexSpongeMode::Absorbing { next_absorb_index: 0 },
        }
    }

    fn absorb(&mut self, input: &[F]) {
        if !input.is_empty() {
            match self.mode {
                DuplexSpongeMode::Absorbing { mut next_absorb_index } => {
                    if next_absorb_index == RATE {
                        self.permute();
                        next_absorb_index = 0;
                    }
                    self.absorb_internal(next_absorb_index, input);
                }
                DuplexSpongeMode::Squeezing { next_squeeze_index: _ } => {
                    self.permute();
                    self.absorb_internal(0, input);
                }
            }
        }
    }

    fn squeeze(&mut self, num_elements: usize) -> SmallVec<[F; 10]> {
        if num_elements == 0 {
            return SmallVec::new();
        }
        let mut output = if num_elements <= 10 {
            smallvec::smallvec_inline![F::zero(); 10]
        } else {
            smallvec::smallvec![F::zero(); num_elements]
        };

        match self.mode {
            DuplexSpongeMode::Absorbing { next_absorb_index: _ } => {
                self.permute();
                self.squeeze_internal(0, &mut output[..num_elements]);
            }
            DuplexSpongeMode::Squeezing { mut next_squeeze_index } => {
                if next_squeeze_index == RATE {
                    self.permute();
                    next_squeeze_index = 0;
                }
                self.squeeze_internal(next_squeeze_index, &mut output[..num_elements]);
            }
        }

        output.truncate(num_elements);
        output
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> PoseidonSponge<F, RATE, CAPACITY> {
    #[inline]
    fn apply_ark(&mut self, round_number: usize) {
        for (state_elem, ark_elem) in self.state.iter_mut().zip(&self.parameters.ark[round_number]) {
            *state_elem += ark_elem;
        }
    }

    #[inline]
    fn apply_s_box(&mut self, is_full_round: bool) {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for elem in self.state.iter_mut() {
                *elem = elem.pow(&[self.parameters.alpha]);
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the first element of state
        else {
            self.state[0] = self.state[0].pow(&[self.parameters.alpha]);
        }
    }

    #[inline]
    fn apply_mds(&mut self) {
        let mut new_state = State::default();
        new_state.iter_mut().zip(&self.parameters.mds).for_each(|(new_elem, mds_row)| {
            *new_elem = self.state.iter().zip(mds_row).map(|(state_elem, &mds_elem)| mds_elem * state_elem).sum::<F>();
        });
        self.state = new_state;
    }

    #[inline]
    fn permute(&mut self) {
        // Determine the partial rounds range bound.
        let partial_rounds = self.parameters.partial_rounds;
        let full_rounds = self.parameters.full_rounds;
        let full_rounds_over_2 = full_rounds / 2;
        let partial_round_range = full_rounds_over_2..(full_rounds_over_2 + partial_rounds);

        // Iterate through all rounds to permute.
        for i in 0..(partial_rounds + full_rounds) {
            let is_full_round = !partial_round_range.contains(&i);
            self.apply_ark(i);
            self.apply_s_box(is_full_round);
            self.apply_mds();
        }
    }

    /// Absorbs everything in elements, this does not end in an absorption.
    #[inline]
    fn absorb_internal(&mut self, mut rate_start: usize, input: &[F]) {
        if !input.is_empty() {
            let first_chunk_size = std::cmp::min(RATE - rate_start, input.len());
            let num_elements_remaining = input.len() - first_chunk_size;
            let (first_chunk, rest_chunk) = input.split_at(first_chunk_size);
            let rest_chunks = rest_chunk.chunks(RATE);
            // The total number of chunks is `elements[num_elements_remaining..].len() / RATE`, plus 1
            // for the remainder.
            let total_num_chunks = 1 + // 1 for the first chunk
                // We add all the chunks that are perfectly divisible by `RATE`
                (num_elements_remaining / RATE) +
                // And also add 1 if the last chunk is non-empty
                // (i.e. if `num_elements_remaining` is not a multiple of `RATE`)
                usize::from((num_elements_remaining % RATE) != 0);

            // Absorb the input elements, `RATE` elements at a time, except for the first chunk, which
            // is of size `RATE - rate_start`.
            for (i, chunk) in std::iter::once(first_chunk).chain(rest_chunks).enumerate() {
                for (element, state_elem) in chunk.iter().zip(&mut self.state.rate_state[rate_start..]) {
                    *state_elem += element;
                }
                // Are we in the last chunk?
                // If so, let's wrap up.
                if i == total_num_chunks - 1 {
                    self.mode = DuplexSpongeMode::Absorbing { next_absorb_index: rate_start + chunk.len() };
                    return;
                } else {
                    self.permute();
                }
                rate_start = 0;
            }
        }
    }

    /// Squeeze |output| many elements. This does not end in a squeeze
    #[inline]
    fn squeeze_internal(&mut self, mut rate_start: usize, output: &mut [F]) {
        let output_size = output.len();
        if output_size != 0 {
            let first_chunk_size = std::cmp::min(RATE - rate_start, output.len());
            let num_output_remaining = output.len() - first_chunk_size;
            let (first_chunk, rest_chunk) = output.split_at_mut(first_chunk_size);
            assert_eq!(rest_chunk.len(), num_output_remaining);
            let rest_chunks = rest_chunk.chunks_mut(RATE);
            // The total number of chunks is `output[num_output_remaining..].len() / RATE`, plus 1
            // for the remainder.
            let total_num_chunks = 1 + // 1 for the first chunk
                // We add all the chunks that are perfectly divisible by `RATE`
                (num_output_remaining / RATE) +
                // And also add 1 if the last chunk is non-empty
                // (i.e. if `num_output_remaining` is not a multiple of `RATE`)
                usize::from((num_output_remaining % RATE) != 0);

            // Absorb the input output, `RATE` output at a time, except for the first chunk, which
            // is of size `RATE - rate_start`.
            for (i, chunk) in std::iter::once(first_chunk).chain(rest_chunks).enumerate() {
                let range = rate_start..(rate_start + chunk.len());
                debug_assert_eq!(
                    chunk.len(),
                    self.state.rate_state[range.clone()].len(),
                    "failed with squeeze {} at rate {} and rate_start {}",
                    output_size,
                    RATE,
                    rate_start
                );
                chunk.copy_from_slice(&self.state.rate_state[range]);
                // Are we in the last chunk?
                // If so, let's wrap up.
                if i == total_num_chunks - 1 {
                    self.mode = DuplexSpongeMode::Squeezing { next_squeeze_index: (rate_start + chunk.len()) };
                    return;
                } else {
                    self.permute();
                }
                rate_start = 0;
            }
        }
    }
}
