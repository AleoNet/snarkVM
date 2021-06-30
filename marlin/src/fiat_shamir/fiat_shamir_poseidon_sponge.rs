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

//
// Acknowledgements
//
// This implementation of Poseidon is entirely from Fractal's implementation
// ([COS20]: https://eprint.iacr.org/2019/1076) with small syntax changes.
//

use crate::fiat_shamir::AlgebraicSponge;
use snarkvm_fields::{PoseidonMDSField, PrimeField};

use rand_core::SeedableRng;

#[derive(Clone)]
pub(super) enum PoseidonSpongeState {
    Absorbing { next_absorb_index: usize },
    Squeezing { next_squeeze_index: usize },
}

#[derive(Clone)]
/// The sponge for Poseidon
pub struct PoseidonSponge<F: PrimeField + PoseidonMDSField> {
    /// Number of rounds in a full-round operation
    pub(super) full_rounds: u32,
    /// number of rounds in a partial-round operation
    pub(super) partial_rounds: u32,
    /// Exponent used in S-boxes
    pub(super) alpha: u64,
    /// Additive Round keys. These are added before each MDS matrix application to make it an affine shift.
    /// They are indexed by ark[round_num][state_element_index]
    pub(super) ark: Vec<Vec<F>>,
    /// Maximally Distance Separating Matrix.
    pub(super) mds: Vec<Vec<F>>,

    /// The sponge's state
    pub(super) state: Vec<F>,
    /// The rate
    pub(super) rate: usize,
    /// The capacity
    pub(super) capacity: usize,
    /// The mode
    pub(super) mode: PoseidonSpongeState,
}

impl<F: PrimeField + PoseidonMDSField> PoseidonSponge<F> {
    fn apply_s_box(&self, state: &mut [F], is_full_round: bool) {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for elem in state {
                *elem = elem.pow(&[self.alpha]);
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the final element of state
        else {
            state[state.len() - 1] = state[state.len() - 1].pow(&[self.alpha]);
        }
    }

    fn apply_ark(&self, state: &mut [F], round_number: usize) {
        for (i, state_elem) in state.iter_mut().enumerate() {
            state_elem.add_assign(self.ark[round_number][i]);
        }
    }

    fn apply_mds(&self, state: &mut [F]) {
        let mut new_state = Vec::new();
        for i in 0..state.len() {
            let mut cur = F::zero();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem.mul(&self.mds[i][j]);
                cur.add_assign(term);
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()])
    }

    fn permute(&mut self) {
        let full_rounds_over_2 = self.full_rounds / 2;
        let mut state = self.state.clone();
        for i in 0..full_rounds_over_2 {
            self.apply_ark(&mut state, i as usize);
            self.apply_s_box(&mut state, true);
            self.apply_mds(&mut state);
        }

        for i in full_rounds_over_2..(full_rounds_over_2 + self.partial_rounds) {
            self.apply_ark(&mut state, i as usize);
            self.apply_s_box(&mut state, false);
            self.apply_mds(&mut state);
        }

        for i in (full_rounds_over_2 + self.partial_rounds)..(self.partial_rounds + self.full_rounds) {
            self.apply_ark(&mut state, i as usize);
            self.apply_s_box(&mut state, true);
            self.apply_mds(&mut state);
        }
        self.state = state;
    }

    // Absorbs everything in elements, this does not end in an absorbtion.
    fn absorb_internal(&mut self, rate_start_index: usize, elements: &[F]) {
        // if we can finish in this call
        if rate_start_index + elements.len() <= self.rate {
            for (i, element) in elements.iter().enumerate() {
                self.state[i + rate_start_index] += element;
            }
            self.mode = PoseidonSpongeState::Absorbing {
                next_absorb_index: rate_start_index + elements.len(),
            };

            return;
        }
        // otherwise absorb (rate - rate_start_index) elements
        let num_elements_absorbed = self.rate - rate_start_index;
        for (i, element) in elements.iter().enumerate().take(num_elements_absorbed) {
            self.state[i + rate_start_index] += element;
        }
        self.permute();
        // Tail recurse, with the input elements being truncated by num elements absorbed
        self.absorb_internal(0, &elements[num_elements_absorbed..]);
    }

    // Squeeze |output| many elements. This does not end in a squeeze
    fn squeeze_internal(&mut self, rate_start_index: usize, output: &mut [F]) {
        // if we can finish in this call
        if rate_start_index + output.len() <= self.rate {
            output.clone_from_slice(&self.state[rate_start_index..(output.len() + rate_start_index)]);
            self.mode = PoseidonSpongeState::Squeezing {
                next_squeeze_index: rate_start_index + output.len(),
            };
            return;
        }
        // otherwise squeeze (rate - rate_start_index) elements
        let num_elements_squeezed = self.rate - rate_start_index;
        output[..num_elements_squeezed]
            .clone_from_slice(&self.state[rate_start_index..(num_elements_squeezed + rate_start_index)]);

        // Unless we are done with squeezing in this call, permute.
        if output.len() != self.rate {
            self.permute();
        }
        // Tail recurse, with the correct change to indices in output happening due to changing the slice
        self.squeeze_internal(0, &mut output[num_elements_squeezed..]);
    }
}

impl<F: PrimeField + PoseidonMDSField> AlgebraicSponge<F> for PoseidonSponge<F> {
    fn new() -> Self {
        // The parameters are checked for BLS12-377's Fq field (where the Marlin sponge actually runs over)
        let full_rounds = F::poseidon_number_full_rounds();
        let partial_rounds = F::poseidon_number_partial_rounds();
        let alpha = F::poseidon_alpha();

        // This MDS matrix passes the checks in the reference implementation.
        let mds = F::poseidon_mds_matrix();

        let mut ark = Vec::new();
        let mut ark_rng = rand_chacha::ChaChaRng::seed_from_u64(123456789u64);

        for _ in 0..(full_rounds + partial_rounds) {
            let mut res = Vec::new();

            for _ in 0..3 {
                res.push(F::rand(&mut ark_rng));
            }
            ark.push(res);
        }

        let rate = 2;
        let capacity = 1;
        let state = vec![F::zero(); rate + capacity];
        let mode = PoseidonSpongeState::Absorbing { next_absorb_index: 0 };

        PoseidonSponge {
            full_rounds,
            partial_rounds,
            alpha,
            ark,
            mds,

            state,
            rate,
            capacity,
            mode,
        }
    }

    fn absorb(&mut self, elems: &[F]) {
        if elems.is_empty() {
            return;
        }

        match self.mode {
            PoseidonSpongeState::Absorbing { next_absorb_index } => {
                let mut absorb_index = next_absorb_index;
                if absorb_index == self.rate {
                    self.permute();
                    absorb_index = 0;
                }
                self.absorb_internal(absorb_index, elems);
            }
            PoseidonSpongeState::Squeezing { next_squeeze_index: _ } => {
                self.permute();
                self.absorb_internal(0, elems);
            }
        };
    }

    fn squeeze(&mut self, num: usize) -> Vec<F> {
        let mut squeezed_elems = vec![F::zero(); num];
        match self.mode {
            PoseidonSpongeState::Absorbing { next_absorb_index: _ } => {
                self.permute();
                self.squeeze_internal(0, &mut squeezed_elems);
            }
            PoseidonSpongeState::Squeezing { next_squeeze_index } => {
                let mut squeeze_index = next_squeeze_index;
                if squeeze_index == self.rate {
                    self.permute();
                    squeeze_index = 0;
                }
                self.squeeze_internal(squeeze_index, &mut squeezed_elems);
            }
        };
        squeezed_elems
    }
}
