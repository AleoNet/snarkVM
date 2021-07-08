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

use crate::{CryptographicSpongeVar, FieldGadget, FpGadget};
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_sponge::{
    poseidon::{PoseidonParameters, PoseidonSponge},
    DuplexSpongeMode,
};

#[derive(Clone)]
/// the gadget for Poseidon sponge
///
/// This implementation of Poseidon is entirely from Fractal's implementation in [COS20][cos]
/// with small syntax changes.
///
/// [cos]: https://eprint.iacr.org/2019/1076
pub struct PoseidonSpongeVar<F: PrimeField> {
    /// Sponge Parameters
    pub parameters: PoseidonParameters<F>,

    // Sponge State
    /// the sponge's state
    pub state: Vec<FpGadget<F>>,
    /// the mode
    pub mode: DuplexSpongeMode,
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
                *state_item =
                    state_item.pow_by_constant(cs.ns(|| format!("full round {}", i)), &[self.parameters.alpha])?;
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the first element of state
        else {
            state[0] = state[0].pow_by_constant(cs.ns(|| "partial round"), &[self.parameters.alpha])?;
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
            state_elem.add_constant_in_place(
                cs.ns(|| format!("add ark in place {}", i)),
                &self.parameters.ark[round_number][i],
            )?;
        }
        Ok(())
    }

    fn apply_mds<CS: ConstraintSystem<F>>(&self, mut cs: CS, state: &mut [FpGadget<F>]) -> Result<(), SynthesisError> {
        let mut new_state = Vec::new();
        let zero = FpGadget::<F>::zero(cs.ns(|| "zero"))?;
        for i in 0..state.len() {
            let mut cur = zero.clone();
            for (j, state_elem) in state.iter().enumerate() {
                let term =
                    state_elem.mul_by_constant(cs.ns(|| format!("mul {} {}", i, j)), &self.parameters.mds[i][j])?;
                cur.add_in_place(cs.ns(|| format!("add {} {}", i, j)), &term)?;
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()]);
        Ok(())
    }

    fn permute<CS: ConstraintSystem<F>>(&mut self, mut cs: CS) -> Result<(), SynthesisError> {
        let full_rounds_over_2 = self.parameters.full_rounds / 2;
        let mut state = self.state.clone();
        for i in 0..full_rounds_over_2 {
            self.apply_ark(cs.ns(|| format!("apply_ark {}", i)), &mut state, i)?;
            self.apply_s_box(cs.ns(|| format!("apply_s_box {}", i)), &mut state, true)?;
            self.apply_mds(cs.ns(|| format!("apply_mds {}", i)), &mut state)?;
        }
        for i in full_rounds_over_2..(full_rounds_over_2 + self.parameters.partial_rounds) {
            self.apply_ark(cs.ns(|| format!("apply_ark {}", i)), &mut state, i)?;
            self.apply_s_box(cs.ns(|| format!("apply_s_box {}", i)), &mut state, false)?;
            self.apply_mds(cs.ns(|| format!("apply_mds {}", i)), &mut state)?;
        }

        for i in (full_rounds_over_2 + self.parameters.partial_rounds)
            ..(self.parameters.partial_rounds + self.parameters.full_rounds)
        {
            self.apply_ark(cs.ns(|| format!("apply_ark {}", i)), &mut state, i)?;
            self.apply_s_box(cs.ns(|| format!("apply_s_box {}", i)), &mut state, true)?;
            self.apply_mds(cs.ns(|| format!("apply_mds {}", i)), &mut state)?;
        }

        self.state = state;
        Ok(())
    }

    fn absorb_internal<CS: ConstraintSystem<F>>(
        &mut self,
        mut cs: CS,
        mut rate_start_index: usize,
        elements: &[FpGadget<F>],
    ) -> Result<(), SynthesisError> {
        if elements.len() == 0 {
            return Ok(());
        }

        let mut remaining_elements = elements;

        let mut loop_counter = 0;
        loop {
            // if we can finish in this call
            if rate_start_index + remaining_elements.len() <= self.parameters.rate {
                for (i, element) in remaining_elements.iter().enumerate() {
                    self.state[self.parameters.capacity + i + rate_start_index]
                        .add_in_place(cs.ns(|| format!("absorb {} {}", loop_counter, i)), &element)?;
                }
                self.mode = DuplexSpongeMode::Absorbing {
                    next_absorb_index: rate_start_index + remaining_elements.len(),
                };

                return Ok(());
            }
            // otherwise absorb (rate - rate_start_index) elements
            let num_elements_absorbed = self.parameters.rate - rate_start_index;
            for (i, element) in remaining_elements.iter().enumerate().take(num_elements_absorbed) {
                self.state[self.parameters.capacity + i + rate_start_index]
                    .add_in_place(cs.ns(|| format!("absorb {} {}", loop_counter, i)), &element)?;
            }
            self.permute(cs.ns(|| format!("permute {}", loop_counter)))?;
            // the input elements got truncated by num elements absorbed
            remaining_elements = &remaining_elements[num_elements_absorbed..];
            rate_start_index = 0;

            loop_counter += 1;
        }
    }

    fn squeeze_internal<CS: ConstraintSystem<F>>(
        &mut self,
        mut cs: CS,
        mut rate_start_index: usize,
        output: &mut [FpGadget<F>],
    ) -> Result<(), SynthesisError> {
        let mut remaining_output = output;

        let mut loop_counter = 0;
        loop {
            // if we can finish in this call
            if rate_start_index + remaining_output.len() <= self.parameters.rate {
                remaining_output.clone_from_slice(
                    &self.state[self.parameters.capacity + rate_start_index
                        ..(self.parameters.capacity + remaining_output.len() + rate_start_index)],
                );
                self.mode = DuplexSpongeMode::Squeezing {
                    next_squeeze_index: rate_start_index + remaining_output.len(),
                };
                return Ok(());
            }
            // otherwise squeeze (rate - rate_start_index) elements
            let num_elements_squeezed = self.parameters.rate - rate_start_index;
            remaining_output[..num_elements_squeezed].clone_from_slice(
                &self.state[self.parameters.capacity + rate_start_index
                    ..(self.parameters.capacity + num_elements_squeezed + rate_start_index)],
            );

            // Unless we are done with squeezing in this call, permute.
            if remaining_output.len() != self.parameters.rate {
                self.permute(cs.ns(|| format!("permute {}", loop_counter)))?;
            }
            // Repeat with updated output slices and rate start index
            remaining_output = &mut remaining_output[num_elements_squeezed..];
            rate_start_index = 0;

            loop_counter += 1;
        }
    }
}

impl<F: PrimeField> CryptographicSpongeVar<F, PoseidonSponge<F>> for PoseidonSpongeVar<F> {
    type Parameters = PoseidonParameters<F>;

    fn new<CS: ConstraintSystem<F>>(mut cs: CS, parameters: &Self::Parameters) -> Self {
        let zero = FpGadget::<F>::zero(cs.ns(|| "zero")).unwrap();
        let state = vec![zero; parameters.rate + parameters.capacity];
        let mode = DuplexSpongeMode::Absorbing { next_absorb_index: 0 };

        Self {
            parameters: parameters.clone(),
            state,
            mode,
        }
    }

    fn absorb<'a, CS: ConstraintSystem<F>, I: Iterator<Item = &'a FpGadget<F>>>(
        &mut self,
        mut cs: CS,
        input: I,
    ) -> Result<(), SynthesisError> {
        let input = {
            let mut res = Vec::<FpGadget<F>>::new();
            for i in input {
                res.push(i.clone())
            }
            res
        };

        if input.len() == 0 {
            return Ok(());
        }

        match self.mode {
            DuplexSpongeMode::Absorbing { next_absorb_index } => {
                let mut absorb_index = next_absorb_index;
                if absorb_index == self.parameters.rate {
                    self.permute(cs.ns(|| "absorb permute"))?;
                    absorb_index = 0;
                }
                self.absorb_internal(cs.ns(|| "absorb internal"), absorb_index, &input)?;
            }
            DuplexSpongeMode::Squeezing { next_squeeze_index: _ } => {
                self.permute(cs.ns(|| "squeeze permute"))?;
                self.absorb_internal(cs.ns(|| "absorb internal"), 0, &input)?;
            }
        };

        Ok(())
    }

    fn squeeze_field_elements<CS: ConstraintSystem<F>>(
        &mut self,
        mut cs: CS,
        num_elements: usize,
    ) -> Result<Vec<FpGadget<F>>, SynthesisError> {
        let zero = FpGadget::<F>::zero(cs.ns(|| "zero"))?;
        let mut squeezed_elems = vec![zero; num_elements];
        match self.mode {
            DuplexSpongeMode::Absorbing { next_absorb_index: _ } => {
                self.permute(cs.ns(|| "absorb permute"))?;
                self.squeeze_internal(cs.ns(|| "squeeze internal"), 0, &mut squeezed_elems)?;
            }
            DuplexSpongeMode::Squeezing { next_squeeze_index } => {
                let mut squeeze_index = next_squeeze_index;
                if squeeze_index == self.parameters.rate {
                    self.permute(cs.ns(|| "squeeze permute"))?;
                    squeeze_index = 0;
                }
                self.squeeze_internal(cs.ns(|| "squeeze internal"), squeeze_index, &mut squeezed_elems)?;
            }
        };

        Ok(squeezed_elems)
    }
}

#[cfg(test)]
mod tests {
    use crate::{sponge::PoseidonSpongeVar, AllocGadget, CryptographicSpongeVar, FieldGadget, FpGadget};
    use snarkvm_curves::bls12_377::Fr;
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
    use snarkvm_sponge::{poseidon::PoseidonSponge, CryptographicSponge, PoseidonDefaultParametersField};
    use snarkvm_utilities::{test_rng, UniformRand};

    #[test]
    fn absorb_test() {
        let mut rng = test_rng();

        let mut cs = TestConstraintSystem::<Fr>::new();

        let absorb: Vec<_> = (0..256).map(|_| Fr::rand(&mut rng)).collect();
        let absorb_var: Vec<_> = absorb
            .iter()
            .enumerate()
            .map(|(i, v)| {
                FpGadget::<Fr>::alloc_input(cs.ns(|| format!("alloc input {}", i)), || Ok((*v).clone())).unwrap()
            })
            .collect();

        let sponge_params = Fr::get_default_poseidon_parameters(2, false).unwrap();

        let mut native_sponge = PoseidonSponge::<Fr>::new(&sponge_params);
        let mut constraint_sponge = PoseidonSpongeVar::<Fr>::new(cs.ns(|| "new sponge"), &sponge_params);

        native_sponge.absorb(&absorb);
        constraint_sponge.absorb(cs.ns(|| "absorb"), absorb_var.iter()).unwrap();

        let native_squeeze = native_sponge.squeeze_field_elements(1);
        let constraint_squeeze = constraint_sponge
            .squeeze_field_elements(cs.ns(|| "squeeze"), 1)
            .unwrap();

        assert_eq!(constraint_squeeze[0].get_value().unwrap(), native_squeeze[0]);
        assert!(cs.is_satisfied());
    }
}
