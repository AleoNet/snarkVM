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

// /*
//  * credit:
//  *      This implementation of Poseidon is entirely from Fractal's implementation
//  *      ([COS20]: https://eprint.iacr.org/2019/1076)
//  *      with small syntax changes.
//  */
//
// use crate::fiat_shamir::constraints::AlgebraicSpongeVar;
// use crate::fiat_shamir::poseidon::{PoseidonSponge, PoseidonSpongeState};
// use crate::Vec;
// use ark_ff::PrimeField;
// use ark_r1cs_std::fields::fp::FpVar;
// use ark_r1cs_std::prelude::*;
// use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
// use ark_std::rand::SeedableRng;
//
// #[derive(Clone)]
// /// the gadget for Poseidon sponge
// pub struct PoseidonSpongeVar<F: PrimeField> {
//     /// constraint system
//     pub cs: ConstraintSystemRef<F>,
//     /// number of rounds in a full-round operation
//     pub full_rounds: u32,
//     /// number of rounds in a partial-round operation
//     pub partial_rounds: u32,
//     /// Exponent used in S-boxes
//     pub alpha: u64,
//     /// Additive Round keys. These are added before each MDS matrix application to make it an affine shift.
//     /// They are indexed by ark[round_num][state_element_index]
//     pub ark: Vec<Vec<F>>,
//     /// Maximally Distance Separating Matrix.
//     pub mds: Vec<Vec<F>>,
//
//     /// the sponge's state
//     pub state: Vec<FpVar<F>>,
//     /// the rate
//     pub rate: usize,
//     /// the capacity
//     pub capacity: usize,
//     /// the mode
//     mode: PoseidonSpongeState,
// }
//
// impl<F: PrimeField> PoseidonSpongeVar<F> {
//     #[tracing::instrument(target = "r1cs", skip(self))]
//     fn apply_s_box(
//         &self,
//         state: &mut [FpVar<F>],
//         is_full_round: bool,
//     ) -> Result<(), SynthesisError> {
//         // Full rounds apply the S Box (x^alpha) to every element of state
//         if is_full_round {
//             for state_item in state.iter_mut() {
//                 *state_item = state_item.pow_by_constant(&[self.alpha])?;
//             }
//         }
//         // Partial rounds apply the S Box (x^alpha) to just the final element of state
//         else {
//             state[state.len() - 1] = state[state.len() - 1].pow_by_constant(&[self.alpha])?;
//         }
//
//         Ok(())
//     }
//
//     #[tracing::instrument(target = "r1cs", skip(self))]
//     fn apply_ark(&self, state: &mut [FpVar<F>], round_number: usize) -> Result<(), SynthesisError> {
//         for (i, state_elem) in state.iter_mut().enumerate() {
//             *state_elem += self.ark[round_number][i];
//         }
//         Ok(())
//     }
//
//     #[tracing::instrument(target = "r1cs", skip(self))]
//     fn apply_mds(&self, state: &mut [FpVar<F>]) -> Result<(), SynthesisError> {
//         let mut new_state = Vec::new();
//         let zero = FpVar::<F>::zero();
//         for i in 0..state.len() {
//             let mut cur = zero.clone();
//             for (j, state_elem) in state.iter().enumerate() {
//                 let term = state_elem * self.mds[i][j];
//                 cur += &term;
//             }
//             new_state.push(cur);
//         }
//         state.clone_from_slice(&new_state[..state.len()]);
//         Ok(())
//     }
//
//     #[tracing::instrument(target = "r1cs", skip(self))]
//     fn permute(&mut self) -> Result<(), SynthesisError> {
//         let full_rounds_over_2 = self.full_rounds / 2;
//         let mut state = self.state.clone();
//         for i in 0..full_rounds_over_2 {
//             self.apply_ark(&mut state, i as usize)?;
//             self.apply_s_box(&mut state, true)?;
//             self.apply_mds(&mut state)?;
//         }
//         for i in full_rounds_over_2..(full_rounds_over_2 + self.partial_rounds) {
//             self.apply_ark(&mut state, i as usize)?;
//             self.apply_s_box(&mut state, false)?;
//             self.apply_mds(&mut state)?;
//         }
//
//         for i in
//             (full_rounds_over_2 + self.partial_rounds)..(self.partial_rounds + self.full_rounds)
//         {
//             self.apply_ark(&mut state, i as usize)?;
//             self.apply_s_box(&mut state, true)?;
//             self.apply_mds(&mut state)?;
//         }
//
//         self.state = state;
//         Ok(())
//     }
//
//     #[tracing::instrument(target = "r1cs", skip(self))]
//     fn absorb_internal(
//         &mut self,
//         rate_start_index: usize,
//         elements: &[FpVar<F>],
//     ) -> Result<(), SynthesisError> {
//         // if we can finish in this call
//         if rate_start_index + elements.len() <= self.rate {
//             for (i, element) in elements.iter().enumerate() {
//                 self.state[i + rate_start_index] += element;
//             }
//             self.mode = PoseidonSpongeState::Absorbing {
//                 next_absorb_index: rate_start_index + elements.len(),
//             };
//
//             return Ok(());
//         }
//         // otherwise absorb (rate - rate_start_index) elements
//         let num_elements_absorbed = self.rate - rate_start_index;
//         for (i, element) in elements.iter().enumerate().take(num_elements_absorbed) {
//             self.state[i + rate_start_index] += element;
//         }
//         self.permute()?;
//         // Tail recurse, with the input elements being truncated by num elements absorbed
//         self.absorb_internal(0, &elements[num_elements_absorbed..])
//     }
//
//     // Squeeze |output| many elements. This does not end in a squeeze
//     #[tracing::instrument(target = "r1cs", skip(self))]
//     fn squeeze_internal(
//         &mut self,
//         rate_start_index: usize,
//         output: &mut [FpVar<F>],
//     ) -> Result<(), SynthesisError> {
//         // if we can finish in this call
//         if rate_start_index + output.len() <= self.rate {
//             output
//                 .clone_from_slice(&self.state[rate_start_index..(output.len() + rate_start_index)]);
//             self.mode = PoseidonSpongeState::Squeezing {
//                 next_squeeze_index: rate_start_index + output.len(),
//             };
//             return Ok(());
//         }
//         // otherwise squeeze (rate - rate_start_index) elements
//         let num_elements_squeezed = self.rate - rate_start_index;
//         output[..num_elements_squeezed].clone_from_slice(
//             &self.state[rate_start_index..(num_elements_squeezed + rate_start_index)],
//         );
//
//         // Unless we are done with squeezing in this call, permute.
//         if output.len() != self.rate {
//             self.permute()?;
//         }
//         // Tail recurse, with the correct change to indices in output happening due to changing the slice
//         self.squeeze_internal(0, &mut output[num_elements_squeezed..])
//     }
// }
//
// impl<F: PrimeField> AlgebraicSpongeVar<F, PoseidonSponge<F>> for PoseidonSpongeVar<F> {
//     fn new(cs: ConstraintSystemRef<F>) -> Self {
//         // Requires F to be Alt_Bn128Fr
//         let full_rounds = 8;
//         let partial_rounds = 31;
//         let alpha = 17;
//
//         let mds = vec![
//             vec![F::one(), F::zero(), F::one()],
//             vec![F::one(), F::one(), F::zero()],
//             vec![F::zero(), F::one(), F::one()],
//         ];
//
//         let mut ark = Vec::new();
//         let mut ark_rng = rand_chacha::ChaChaRng::seed_from_u64(123456789u64);
//
//         for _ in 0..(full_rounds + partial_rounds) {
//             let mut res = Vec::new();
//
//             for _ in 0..3 {
//                 res.push(F::rand(&mut ark_rng));
//             }
//             ark.push(res);
//         }
//
//         let rate = 2;
//         let capacity = 1;
//         let zero = FpVar::<F>::zero();
//         let state = vec![zero; rate + capacity];
//         let mode = PoseidonSpongeState::Absorbing {
//             next_absorb_index: 0,
//         };
//
//         Self {
//             cs,
//             full_rounds,
//             partial_rounds,
//             alpha,
//             ark,
//             mds,
//
//             state,
//             rate,
//             capacity,
//             mode,
//         }
//     }
//
//     fn constant(cs: ConstraintSystemRef<F>, pfs: &PoseidonSponge<F>) -> Self {
//         let mut state_gadgets = Vec::new();
//
//         for state_elem in pfs.state.iter() {
//             state_gadgets.push(
//                 FpVar::<F>::new_constant(ark_relations::ns!(cs, "alloc_elems"), *state_elem)
//                     .unwrap(),
//             );
//         }
//
//         Self {
//             cs,
//             full_rounds: pfs.full_rounds,
//             partial_rounds: pfs.partial_rounds,
//             alpha: pfs.alpha,
//             ark: pfs.ark.clone(),
//             mds: pfs.mds.clone(),
//
//             state: state_gadgets,
//             rate: pfs.rate,
//             capacity: pfs.capacity,
//             mode: pfs.mode.clone(),
//         }
//     }
//
//     fn cs(&self) -> ConstraintSystemRef<F> {
//         self.cs.clone()
//     }
//
//     fn absorb(&mut self, elems: &[FpVar<F>]) -> Result<(), SynthesisError> {
//         if elems.is_empty() {
//             return Ok(());
//         }
//
//         match self.mode {
//             PoseidonSpongeState::Absorbing { next_absorb_index } => {
//                 let mut absorb_index = next_absorb_index;
//                 if absorb_index == self.rate {
//                     self.permute()?;
//                     absorb_index = 0;
//                 }
//                 self.absorb_internal(absorb_index, elems)?;
//             }
//             PoseidonSpongeState::Squeezing {
//                 next_squeeze_index: _,
//             } => {
//                 self.permute()?;
//                 self.absorb_internal(0, elems)?;
//             }
//         };
//
//         Ok(())
//     }
//
//     fn squeeze(&mut self, num: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
//         let zero = FpVar::zero();
//         let mut squeezed_elems = vec![zero; num];
//         match self.mode {
//             PoseidonSpongeState::Absorbing {
//                 next_absorb_index: _,
//             } => {
//                 self.permute()?;
//                 self.squeeze_internal(0, &mut squeezed_elems)?;
//             }
//             PoseidonSpongeState::Squeezing { next_squeeze_index } => {
//                 let mut squeeze_index = next_squeeze_index;
//                 if squeeze_index == self.rate {
//                     self.permute()?;
//                     squeeze_index = 0;
//                 }
//                 self.squeeze_internal(squeeze_index, &mut squeezed_elems)?;
//             }
//         };
//
//         Ok(squeezed_elems)
//     }
// }
