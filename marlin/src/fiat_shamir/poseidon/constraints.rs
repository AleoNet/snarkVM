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

/*
 * credit:
 *      This implementation of Poseidon is entirely from Fractal's implementation
 *      ([COS20]: https://eprint.iacr.org/2019/1076)
 *      with small syntax changes.
 */

use crate::fiat_shamir::{
    poseidon::{PoseidonSponge, PoseidonSpongeState},
    traits::AlgebraicSpongeVar,
};

use snarkvm_fields::PrimeField;
use snarkvm_gadgets::{fields::FpGadget, traits::fields::FieldGadget, utilities::alloc::AllocGadget};
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};

use rand::SeedableRng;

#[derive(Clone)]
/// the gadget for Poseidon sponge
pub struct PoseidonSpongeVar<F: PrimeField> {
    /// number of rounds in a full-round operation
    pub full_rounds: u32,
    /// number of rounds in a partial-round operation
    pub partial_rounds: u32,
    /// Exponent used in S-boxes
    pub alpha: u64,
    /// Additive Round keys. These are added before each MDS matrix application to make it an affine shift.
    /// They are indexed by ark[round_num][state_element_index]
    pub ark: Vec<Vec<F>>,
    /// Maximally Distance Separating Matrix.
    pub mds: Vec<Vec<F>>,

    /// the sponge's state
    pub state: Vec<FpGadget<F>>,
    /// the rate
    pub rate: usize,
    /// the capacity
    pub capacity: usize,
    /// the mode
    mode: PoseidonSpongeState,
}

impl<F: PrimeField> PoseidonSpongeVar<F> {
    fn apply_s_box<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        state: &mut [FpGadget<F>],
        is_full_round: bool,
    ) -> Result<(), SynthesisError> {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for (i, state_item) in state.iter_mut().enumerate() {
                *state_item = state_item.pow_by_constant(cs.ns(|| format!("pow_by_constant_{}", i)), &[self.alpha])?;
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the final element of state
        else {
            state[state.len() - 1] =
                state[state.len() - 1].pow_by_constant(cs.ns(|| "pow_by_constant"), &[self.alpha])?;
        }

        Ok(())
    }

    fn apply_ark<CS: ConstraintSystem<F>>(
        &self,
        mut cs: CS,
        state: &mut [FpGadget<F>],
        round_number: usize,
    ) -> Result<(), SynthesisError> {
        for (i, state_elem) in state.iter_mut().enumerate() {
            *state_elem = state_elem.add_constant(cs.ns(|| format!("add_{}", i)), &self.ark[round_number][i])?;
        }
        Ok(())
    }

    fn apply_mds<CS: ConstraintSystem<F>>(&self, mut cs: CS, state: &mut [FpGadget<F>]) -> Result<(), SynthesisError> {
        let mut new_state = Vec::new();
        let zero = FpGadget::<F>::zero(cs.ns(|| "zero"))?;
        for i in 0..state.len() {
            let mut cur = zero.clone();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem
                    .mul_by_constant(cs.ns(|| format!("state_elem_times_mds_{}_{}", i, j)), &self.mds[i][j])?;
                cur = cur.add(cs.ns(|| format!("cur_add_term_{}_{}", i, j)), &term)?;
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()]);
        Ok(())
    }

    fn permute<CS: ConstraintSystem<F>>(&mut self, mut cs: CS) -> Result<(), SynthesisError> {
        let full_rounds_over_2 = self.full_rounds / 2;
        let mut state = self.state.clone();
        for i in 0..full_rounds_over_2 {
            self.apply_ark(cs.ns(|| format!("first_apply_ark_{}", i)), &mut state, i as usize)?;
            self.apply_s_box(cs.ns(|| format!("first_apply_s_box_{}", i)), &mut state, true)?;
            self.apply_mds(cs.ns(|| format!("first_apply_mds_{}", i)), &mut state)?;
        }
        for i in full_rounds_over_2..(full_rounds_over_2 + self.partial_rounds) {
            self.apply_ark(cs.ns(|| format!("second_apply_ark_{}", i)), &mut state, i as usize)?;
            self.apply_s_box(cs.ns(|| format!("second_apply_s_box_{}", i)), &mut state, false)?;
            self.apply_mds(cs.ns(|| format!("second_apply_mds_{}", i)), &mut state)?;
        }

        for i in (full_rounds_over_2 + self.partial_rounds)..(self.partial_rounds + self.full_rounds) {
            self.apply_ark(cs.ns(|| format!("third_apply_ark_{}", i)), &mut state, i as usize)?;
            self.apply_s_box(cs.ns(|| format!("third_apply_s_box_{}", i)), &mut state, true)?;
            self.apply_mds(cs.ns(|| format!("third_apply_mds_{}", i)), &mut state)?;
        }

        self.state = state;
        Ok(())
    }

    fn absorb_internal<CS: ConstraintSystem<F>>(
        &mut self,
        mut cs: CS,
        rate_start_index: usize,
        elements: &[FpGadget<F>],
    ) -> Result<(), SynthesisError> {
        // if we can finish in this call
        if rate_start_index + elements.len() <= self.rate {
            for (i, element) in elements.iter().enumerate() {
                self.state[i + rate_start_index].add_in_place(cs.ns(|| format!("first_add_element_{}", i)), element)?;
            }
            self.mode = PoseidonSpongeState::Absorbing {
                next_absorb_index: rate_start_index + elements.len(),
            };

            return Ok(());
        }
        // otherwise absorb (rate - rate_start_index) elements
        let num_elements_absorbed = self.rate - rate_start_index;
        for (i, element) in elements.iter().enumerate().take(num_elements_absorbed) {
            self.state[i + rate_start_index].add_in_place(cs.ns(|| format!("second_add_element_{}", i)), element)?;
        }
        self.permute(cs.ns(|| "permute"))?;
        // Tail recurse, with the input elements being truncated by num elements absorbed
        self.absorb_internal(cs.ns(|| "absorb_internal"), 0, &elements[num_elements_absorbed..])
    }

    // Squeeze |output| many elements. This does not end in a squeeze
    fn squeeze_internal<CS: ConstraintSystem<F>>(
        &mut self,
        mut cs: CS,
        rate_start_index: usize,
        output: &mut [FpGadget<F>],
    ) -> Result<(), SynthesisError> {
        // if we can finish in this call
        if rate_start_index + output.len() <= self.rate {
            output.clone_from_slice(&self.state[rate_start_index..(output.len() + rate_start_index)]);
            self.mode = PoseidonSpongeState::Squeezing {
                next_squeeze_index: rate_start_index + output.len(),
            };
            return Ok(());
        }
        // otherwise squeeze (rate - rate_start_index) elements
        let num_elements_squeezed = self.rate - rate_start_index;
        output[..num_elements_squeezed]
            .clone_from_slice(&self.state[rate_start_index..(num_elements_squeezed + rate_start_index)]);

        // Unless we are done with squeezing in this call, permute.
        if output.len() != self.rate {
            self.permute(cs.ns(|| "permute"))?;
        }
        // Tail recurse, with the correct change to indices in output happening due to changing the slice
        self.squeeze_internal(cs.ns(|| "squeeze_internal"), 0, &mut output[num_elements_squeezed..])
    }
}

impl<F: PrimeField> AlgebraicSpongeVar<F, PoseidonSponge<F>> for PoseidonSpongeVar<F> {
    fn new<CS: ConstraintSystem<F>>(mut cs: CS) -> Self {
        // Requires F to be Alt_Bn128Fr
        let full_rounds = 8;
        let partial_rounds = 31;
        let alpha = 17;

        let mds = vec![
            vec![F::one(), F::zero(), F::one()],
            vec![F::one(), F::one(), F::zero()],
            vec![F::zero(), F::one(), F::one()],
        ];

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
        let zero = FpGadget::<F>::zero(cs.ns(|| "zero")).unwrap();
        let state = vec![zero; rate + capacity];
        let mode = PoseidonSpongeState::Absorbing { next_absorb_index: 0 };

        Self {
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

    fn constant<CS: ConstraintSystem<F>>(mut cs: CS, pfs: &PoseidonSponge<F>) -> Self {
        let mut state_gadgets = Vec::new();

        for (i, state_elem) in pfs.state.iter().enumerate() {
            state_gadgets.push(
                FpGadget::<F>::alloc_constant(cs.ns(|| format!("alloc_elems_{}", i)), || Ok(*state_elem)).unwrap(),
            );
        }

        Self {
            full_rounds: pfs.full_rounds,
            partial_rounds: pfs.partial_rounds,
            alpha: pfs.alpha,
            ark: pfs.ark.clone(),
            mds: pfs.mds.clone(),

            state: state_gadgets,
            rate: pfs.rate,
            capacity: pfs.capacity,
            mode: pfs.mode.clone(),
        }
    }

    fn absorb<CS: ConstraintSystem<F>>(&mut self, mut cs: CS, elems: &[FpGadget<F>]) -> Result<(), SynthesisError> {
        if elems.is_empty() {
            return Ok(());
        }

        match self.mode {
            PoseidonSpongeState::Absorbing { next_absorb_index } => {
                let mut absorb_index = next_absorb_index;
                if absorb_index == self.rate {
                    self.permute(cs.ns(|| "permute"))?;
                    absorb_index = 0;
                }
                self.absorb_internal(cs.ns(|| "absorb_internal"), absorb_index, elems)?;
            }
            PoseidonSpongeState::Squeezing { next_squeeze_index: _ } => {
                self.permute(cs.ns(|| "permute"))?;
                self.absorb_internal(cs.ns(|| "absorb_internal"), 0, elems)?;
            }
        };

        Ok(())
    }

    fn squeeze<CS: ConstraintSystem<F>>(&mut self, mut cs: CS, num: usize) -> Result<Vec<FpGadget<F>>, SynthesisError> {
        let zero = FpGadget::zero(cs.ns(|| "zero"))?;
        let mut squeezed_elems = vec![zero; num];
        match self.mode {
            PoseidonSpongeState::Absorbing { next_absorb_index: _ } => {
                self.permute(cs.ns(|| "permute"))?;
                self.squeeze_internal(cs.ns(|| "squeeze_internal"), 0, &mut squeezed_elems)?;
            }
            PoseidonSpongeState::Squeezing { next_squeeze_index } => {
                let mut squeeze_index = next_squeeze_index;
                if squeeze_index == self.rate {
                    self.permute(cs.ns(|| "permute"))?;
                    squeeze_index = 0;
                }
                self.squeeze_internal(cs.ns(|| "squeeze_internal"), squeeze_index, &mut squeezed_elems)?;
            }
        };

        Ok(squeezed_elems)
    }
}

mod tests {
    use super::*;
    use crate::fiat_shamir::traits::AlgebraicSponge;

    use rand::Rng;
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_gadgets::utilities::eq::EqGadget;
    use snarkvm_r1cs::TestConstraintSystem;
    use snarkvm_utilities::rand::UniformRand;

    type Sponge = PoseidonSponge<Fr>;
    type SpongeVar = PoseidonSpongeVar<Fr>;

    const MAX_ELEMENTS: usize = 100;
    const ITERATIONS: usize = 100;

    #[test]
    fn test_poseidon_sponge_constant() {
        let mut rng = rand_chacha::ChaChaRng::seed_from_u64(123456789u64);
        let mut cs = TestConstraintSystem::<Fr>::new();

        for i in 0..ITERATIONS {
            // Create a new algebraic sponge.
            let mut sponge = Sponge::new();

            // Generate random elements to absorb.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENTS);
            let elements: Vec<_> = (0..num_elements).map(|_| Fr::rand(&mut rng)).collect();

            // Absorb the random elements.
            sponge.absorb(&elements);

            // Alloc the sponge gadget from a given sponge.
            let mut sponge_gadget = SpongeVar::constant(cs.ns(|| format!("poseidon_sponge_constant_{}", i)), &sponge);

            // Squeeze the elements from the sponge and sponge gadget.
            let sponge_squeeze = sponge.squeeze(num_elements);
            let sponge_gadget_squeeze = sponge_gadget
                .squeeze(cs.ns(|| format!("squeeze_{}", i)), num_elements)
                .unwrap();

            // Check that the squeeze results are equivalent.
            for (j, (gadget, element)) in sponge_gadget_squeeze.iter().zip(sponge_squeeze).enumerate() {
                // Allocate the field gadget from the base element.
                let alloc_element =
                    FpGadget::alloc(cs.ns(|| format!("alloc_field_{}_{}", i, j)), || Ok(element)).unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();
            }
        }
    }

    #[test]
    fn test_poseidon_sponge_squeeze() {
        let mut rng = rand_chacha::ChaChaRng::seed_from_u64(123456789u64);
        let mut cs = TestConstraintSystem::<Fr>::new();

        for i in 0..ITERATIONS {
            // Create a new algebraic sponge.
            let mut sponge = Sponge::new();

            // Alloc the sponge gadget from a given sponge.
            let mut sponge_gadget = SpongeVar::new(cs.ns(|| format!("new_poseidon_sponge_{}", i)));

            // Generate random elements to absorb.
            let num_elements: usize = rng.gen_range(0..MAX_ELEMENTS);
            let elements: Vec<_> = (0..num_elements).map(|_| Fr::rand(&mut rng)).collect();

            let mut element_gadgets = vec![];
            for (j, element) in elements.iter().enumerate() {
                // Allocate the field gadget from the base element.
                let alloc_element =
                    FpGadget::alloc(cs.ns(|| format!("native_alloc_field_{}_{}", i, j)), || Ok(element)).unwrap();

                element_gadgets.push(alloc_element);
            }

            // Absorb the random elements.
            sponge.absorb(&elements);
            sponge_gadget
                .absorb(cs.ns(|| format!("absorb_{}", i)), &element_gadgets)
                .unwrap();

            // Squeeze the elements from the sponge and sponge gadget.
            let sponge_squeeze = sponge.squeeze(num_elements);
            let sponge_gadget_squeeze = sponge_gadget
                .squeeze(cs.ns(|| format!("squeeze_{}", i)), num_elements)
                .unwrap();

            // Check that the squeeze results are equivalent.
            for (j, (gadget, element)) in sponge_gadget_squeeze.iter().zip(sponge_squeeze).enumerate() {
                // Allocate the field gadget from the base element.
                let alloc_element =
                    FpGadget::alloc(cs.ns(|| format!("squeeze_alloc_field_{}_{}", i, j)), || Ok(element)).unwrap();

                // Check that the elements are equivalent.
                gadget
                    .enforce_equal(cs.ns(|| format!("enforce_equal_element_{}_{}", i, j)), &alloc_element)
                    .unwrap();
            }
        }
    }
}
