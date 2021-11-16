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

use crate::{
    crypto_hash::{CryptographicSponge, DuplexSpongeMode, PoseidonGrainLFSR},
    CryptoHash,
};
use snarkvm_fields::{
    Fp256,
    Fp256Parameters,
    Fp384,
    Fp384Parameters,
    Fp768,
    Fp768Parameters,
    PoseidonDefaultParameters,
    PrimeField,
};
use snarkvm_utilities::{FromBytes, ToBytes};

use std::{
    io::{Read, Result as IoResult, Write},
    ops::{Index, IndexMut, Range},
    sync::Arc,
};

/// Parameters and RNG used
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PoseidonParameters<F: PrimeField, const RATE: usize, const CAPACITY: usize> {
    /// number of rounds in a full-round operation
    pub full_rounds: usize,
    /// number of rounds in a partial-round operation
    pub partial_rounds: usize,
    /// Exponent used in S-boxes
    pub alpha: u64,
    /// Additive Round keys. These are added before each MDS matrix application to make it an affine shift.
    /// They are indexed by `ark[round_num][state_element_index]`
    pub ark: Vec<Vec<F>>,
    /// Maximally Distance Separating Matrix.
    pub mds: Vec<Vec<F>>,
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> PoseidonParameters<F, RATE, CAPACITY> {
    /// Initialize the parameter for Poseidon Sponge.
    pub fn new(full_rounds: usize, partial_rounds: usize, alpha: u64, mds: Vec<Vec<F>>, ark: Vec<Vec<F>>) -> Self {
        assert_eq!(ark.len(), full_rounds + partial_rounds);
        for item in &ark {
            assert_eq!(item.len(), RATE + CAPACITY);
        }
        assert_eq!(mds.len(), RATE + CAPACITY);
        for item in &mds {
            assert_eq!(item.len(), RATE + CAPACITY);
        }
        Self {
            full_rounds,
            partial_rounds,
            alpha,
            mds,
            ark,
        }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> ToBytes for PoseidonParameters<F, RATE, CAPACITY> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.full_rounds as u32).write_le(&mut writer)?;
        (self.partial_rounds as u32).write_le(&mut writer)?;
        self.alpha.write_le(&mut writer)?;

        (self.ark.len() as u32).write_le(&mut writer)?;
        for fields in &self.ark {
            (fields.len() as u32).write_le(&mut writer)?;
            for field in fields {
                field.write_le(&mut writer)?;
            }
        }

        (self.mds.len() as u32).write_le(&mut writer)?;
        for fields in &self.mds {
            (fields.len() as u32).write_le(&mut writer)?;
            for field in fields {
                field.write_le(&mut writer)?;
            }
        }

        (RATE as u32).write_le(&mut writer)?;
        (CAPACITY as u32).write_le(&mut writer)
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> FromBytes for PoseidonParameters<F, RATE, CAPACITY> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let full_rounds: u32 = FromBytes::read_le(&mut reader)?;
        let partial_rounds: u32 = FromBytes::read_le(&mut reader)?;
        let alpha: u64 = FromBytes::read_le(&mut reader)?;

        let ark_length: u32 = FromBytes::read_le(&mut reader)?;
        let mut ark = Vec::with_capacity(ark_length as usize);
        for _ in 0..ark_length {
            let num_fields: u32 = FromBytes::read_le(&mut reader)?;
            let mut fields = Vec::with_capacity(num_fields as usize);

            for _ in 0..num_fields {
                let field: F = FromBytes::read_le(&mut reader)?;
                fields.push(field);
            }
            ark.push(fields);
        }

        let mds_length: u32 = FromBytes::read_le(&mut reader)?;
        let mut mds = Vec::with_capacity(mds_length as usize);
        for _ in 0..mds_length {
            let num_fields: u32 = FromBytes::read_le(&mut reader)?;
            let mut fields = Vec::with_capacity(num_fields as usize);

            for _ in 0..num_fields {
                let field: F = FromBytes::read_le(&mut reader)?;
                fields.push(field);
            }
            mds.push(fields);
        }

        let rate: u32 = FromBytes::read_le(&mut reader)?;
        let capacity: u32 = FromBytes::read_le(&mut reader)?;
        if rate != RATE as u32 || capacity != CAPACITY as u32 {
            return Err(std::io::ErrorKind::Other.into());
        }

        Ok(Self::new(
            full_rounds as usize,
            partial_rounds as usize,
            alpha,
            mds,
            ark,
        ))
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
    // Sponge Parameters
    pub parameters: Arc<PoseidonParameters<F, RATE, CAPACITY>>,

    // Sponge State
    /// current sponge's state (current elements in the permutation block)
    pub state: State<F, RATE, CAPACITY>,
    /// current mode (whether its absorbing or squeezing)
    pub mode: DuplexSpongeMode,
}

#[derive(Copy, Clone, Debug)]
pub struct State<F: PrimeField, const RATE: usize, const CAPACITY: usize> {
    capacity_state: [F; CAPACITY],
    rate_state: [F; RATE],
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> Default for State<F, RATE, CAPACITY> {
    fn default() -> Self {
        Self {
            capacity_state: [F::zero(); CAPACITY],
            rate_state: [F::zero(); RATE],
        }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> State<F, RATE, CAPACITY> {
    /// Returns an immutable iterator over the state.
    fn iter(&self) -> impl Iterator<Item = &F> {
        self.capacity_state.iter().chain(self.rate_state.iter())
    }

    /// Returns an mutable iterator over the state.
    fn iter_mut(&mut self) -> impl Iterator<Item = &mut F> {
        self.capacity_state.iter_mut().chain(self.rate_state.iter_mut())
    }

    /// Get elements lying within the specified range
    fn range(&self, range: Range<usize>) -> impl Iterator<Item = &F> {
        let start = range.start;
        let end = range.end;
        assert!(
            start < end,
            "start < end in range: start is {} but end is {}",
            start,
            end
        );
        assert!(
            end <= RATE + CAPACITY,
            "Range out of bounds: range is {:?} but length is {}",
            range,
            RATE + CAPACITY
        );
        if start >= CAPACITY {
            // Our range is contained entirely in `rate_state`
            self.rate_state[(start - CAPACITY)..(end - CAPACITY)].iter().chain(&[]) // This hack is need for `impl Iterator` to work.
        } else if end > CAPACITY {
            // Our range spans both arrays
            self.capacity_state[start..]
                .iter()
                .chain(self.rate_state[..(end - CAPACITY)].iter())
        } else {
            debug_assert!(end <= CAPACITY);
            debug_assert!(start < CAPACITY);
            // Our range spans only the first array
            self.capacity_state[start..end].iter().chain(&[])
        }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> Index<usize> for State<F, RATE, CAPACITY> {
    type Output = F;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(
            index < RATE + CAPACITY,
            "Index out of bounds: index is {} but length is {}",
            index,
            RATE + CAPACITY
        );
        if index < CAPACITY {
            &self.capacity_state[index]
        } else {
            &self.rate_state[index - CAPACITY]
        }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> IndexMut<usize> for State<F, RATE, CAPACITY> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(
            index < RATE + CAPACITY,
            "Index out of bounds: index is {} but length is {}",
            index,
            RATE + CAPACITY
        );
        if index < CAPACITY {
            &mut self.capacity_state[index]
        } else {
            &mut self.rate_state[index - CAPACITY]
        }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> PoseidonSponge<F, RATE, CAPACITY> {
    #[inline]
    fn apply_s_box(&self, state: &mut State<F, RATE, CAPACITY>, is_full_round: bool) {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for elem in state.iter_mut() {
                *elem = elem.pow(&[self.parameters.alpha]);
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the first element of state
        else {
            state[0] = state[0].pow(&[self.parameters.alpha]);
        }
    }

    #[inline]
    fn apply_ark(&self, state: &mut State<F, RATE, CAPACITY>, round_number: usize) {
        for (state_elem, ark_elem) in state.iter_mut().zip(&self.parameters.ark[round_number]) {
            *state_elem += ark_elem;
        }
    }

    #[inline]
    fn apply_mds(&self, state: &mut State<F, RATE, CAPACITY>) {
        let mut new_state = State::default();
        new_state
            .iter_mut()
            .zip(&self.parameters.mds)
            .for_each(|(new_elem, mds_row)| {
                *new_elem = state
                    .iter()
                    .zip(mds_row)
                    .map(|(state_elem, &mds_elem)| mds_elem * state_elem)
                    .sum::<F>();
            });
        *state = new_state;
    }

    fn permute(&mut self) {
        let full_rounds_over_2 = self.parameters.full_rounds / 2;
        let partial_round_range = full_rounds_over_2..(full_rounds_over_2 + self.parameters.partial_rounds);

        let mut state = self.state;
        for i in 0..(self.parameters.partial_rounds + self.parameters.full_rounds) {
            let is_full_round = !partial_round_range.contains(&i);
            self.apply_ark(&mut state, i);
            self.apply_s_box(&mut state, is_full_round);
            self.apply_mds(&mut state);
        }
        self.state = state;
    }

    // Absorbs everything in elements, this does not end in an absorbtion.
    fn absorb_internal(&mut self, rate_start: usize, elements: &[F]) {
        if elements.len() == 0 {
            return;
        }

        let first_chunk_size = std::cmp::min(RATE - rate_start, elements.len());
        let (first_chunk, rest_chunk) = elements.split_at(first_chunk_size);
        let rest_chunks = rest_chunk.chunks(RATE);
        // The total number of chunks is `elements[num_elements_absorbed..].len() / RATE`, plus 1
        // for the remainder.
        let num_elements_remaining = elements.len() - first_chunk_size;
        let total_num_chunks = 1 + // 1 for the first chunk
            // We add all the chunks that are perfectly divisible by `RATE`
            (num_elements_remaining / RATE) +
            // And also add 1 if the last chunk is non-empty 
            // (i.e. if `num_elements_remaining` is not a multiple of `RATE`)
            (num_elements_remaining % RATE) % 2;

        // Absorb the input elements, `RATE` elements at a time, except for the first chunk, which
        // is of size `RATE - rate_start`.
        for (i, chunk) in std::iter::once(first_chunk).chain(rest_chunks).enumerate() {
            for (element, state_elem) in chunk.iter().zip(&mut self.state.rate_state[rate_start..]) {
                *state_elem += element;
            }
            // Are we in the last chunk?
            // If so, let's wrap up.
            if i == total_num_chunks - 1 {
                self.mode = DuplexSpongeMode::Absorbing {
                    next_absorb_index: rate_start + chunk.len(),
                };
                return;
            } else {
                self.permute();
            }
        }
    }

    // Squeeze |output| many elements. This does not end in a squeeze
    fn squeeze_internal(&mut self, mut rate_start_index: usize, output: &mut [F]) {
        let mut output_remaining = output;
        loop {
            // if we can finish in this call
            if rate_start_index + output_remaining.len() <= RATE {
                let start = CAPACITY + rate_start_index;
                let end = start + output_remaining.len();
                output_remaining
                    .iter_mut()
                    .zip(self.state.range(start..end))
                    .for_each(|(out, state)| {
                        *out = *state;
                    });
                self.mode = DuplexSpongeMode::Squeezing {
                    next_squeeze_index: rate_start_index + output_remaining.len(),
                };
                return;
            }
            // otherwise squeeze (rate - rate_start_index) elements
            let num_elements_squeezed = RATE - rate_start_index;
            let start = CAPACITY + rate_start_index;
            let end = start + num_elements_squeezed;
            output_remaining[..num_elements_squeezed]
                .iter_mut()
                .zip(self.state.range(start..end))
                .for_each(|(out, state)| {
                    *out = *state;
                });

            // Unless we are done with squeezing in this call, permute.
            if output_remaining.len() != RATE {
                self.permute();
            }
            // Repeat with updated output slices
            output_remaining = &mut output_remaining[num_elements_squeezed..];
            rate_start_index = 0;
        }
    }
}

impl<F: PrimeField, const RATE: usize, const CAPACITY: usize> CryptographicSponge<F>
    for PoseidonSponge<F, RATE, CAPACITY>
{
    type Parameters = Arc<PoseidonParameters<F, RATE, CAPACITY>>;

    fn new(parameters: &Self::Parameters) -> Self {
        let state = State::default();
        let mode = DuplexSpongeMode::Absorbing { next_absorb_index: 0 };

        Self {
            parameters: parameters.clone(),
            state,
            mode,
        }
    }

    fn absorb(&mut self, input: &[F]) {
        if input.len() == 0 {
            return;
        }

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
        };
    }

    fn squeeze_field_elements(&mut self, num_elements: usize) -> Vec<F> {
        if num_elements == 0 {
            return vec![];
        }
        let mut squeezed_elems = vec![F::zero(); num_elements];
        match self.mode {
            DuplexSpongeMode::Absorbing { next_absorb_index: _ } => {
                self.permute();
                self.squeeze_internal(0, &mut squeezed_elems);
            }
            DuplexSpongeMode::Squeezing { mut next_squeeze_index } => {
                if next_squeeze_index == RATE {
                    self.permute();
                    next_squeeze_index = 0;
                }
                self.squeeze_internal(next_squeeze_index, &mut squeezed_elems);
            }
        };

        squeezed_elems
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoseidonCryptoHash<
    F: PrimeField + PoseidonDefaultParametersField,
    const RATE: usize,
    const OPTIMIZED_FOR_WEIGHTS: bool,
> {
    parameters: Arc<PoseidonParameters<F, RATE, 1>>,
}

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool> CryptoHash
    for PoseidonCryptoHash<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    type Input = F;
    type Output = F;
    type Parameters = PoseidonParameters<F, RATE, 1>;

    /// Initializes a new instance of the cryptographic hash function.
    fn setup() -> Self {
        Self {
            parameters: Arc::new(F::get_default_poseidon_parameters::<RATE>(OPTIMIZED_FOR_WEIGHTS).unwrap()),
        }
    }

    fn evaluate(&self, input: &[Self::Input]) -> Self::Output {
        let mut sponge = PoseidonSponge::<F, RATE, 1>::new(&self.parameters);
        sponge.absorb(input);
        sponge.squeeze_field_elements(1)[0]
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool>
    From<PoseidonParameters<F, RATE, 1>> for PoseidonCryptoHash<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    fn from(parameters: PoseidonParameters<F, RATE, 1>) -> Self {
        Self {
            parameters: Arc::new(parameters),
        }
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool> ToBytes
    for PoseidonCryptoHash<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.parameters.write_le(&mut writer)
    }
}

impl<F: PrimeField + PoseidonDefaultParametersField, const RATE: usize, const OPTIMIZED_FOR_WEIGHTS: bool> FromBytes
    for PoseidonCryptoHash<F, RATE, OPTIMIZED_FOR_WEIGHTS>
{
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let parameters: PoseidonParameters<F, RATE, 1> = FromBytes::read_le(&mut reader)?;
        Ok(Self::from(parameters))
    }
}

/// A field with Poseidon parameters associated
pub trait PoseidonDefaultParametersField: PrimeField {
    /// Obtain the default Poseidon parameters for this rate and for this prime field,
    /// with a specific optimization goal.
    fn get_default_poseidon_parameters<const RATE: usize>(
        optimized_for_weights: bool,
    ) -> Option<PoseidonParameters<Self, RATE, 1>>;
}

/// Internal function that uses the `PoseidonDefaultParameters` to compute the Poseidon parameters.
pub fn get_default_poseidon_parameters_internal<F: PrimeField, P: PoseidonDefaultParameters, const RATE: usize>(
    optimized_for_weights: bool,
) -> Option<PoseidonParameters<F, RATE, 1>> {
    let params_set = if !optimized_for_weights {
        P::PARAMS_OPT_FOR_CONSTRAINTS
    } else {
        P::PARAMS_OPT_FOR_WEIGHTS
    };

    params_set.iter().find(|p| p.rate == RATE).map(|p| {
        let (ark, mds) = find_poseidon_ark_and_mds::<F, RATE>(
            P::MODULUS_BITS as u64,
            p.full_rounds as u64,
            p.partial_rounds as u64,
            p.skip_matrices as u64,
        );

        PoseidonParameters {
            full_rounds: p.full_rounds,
            partial_rounds: p.partial_rounds,
            alpha: p.alpha as u64,
            ark,
            mds,
        }
    })
}

/// Internal function that computes the ark and mds from the Poseidon Grain LFSR.
pub fn find_poseidon_ark_and_mds<F: PrimeField, const RATE: usize>(
    prime_bits: u64,
    full_rounds: u64,
    partial_rounds: u64,
    skip_matrices: u64,
) -> (Vec<Vec<F>>, Vec<Vec<F>>) {
    let mut lfsr = PoseidonGrainLFSR::new(false, prime_bits, (RATE + 1) as u64, full_rounds, partial_rounds);

    let mut ark = Vec::<Vec<F>>::new();
    for _ in 0..(full_rounds + partial_rounds) {
        ark.push(lfsr.get_field_elements_rejection_sampling(RATE + 1));
    }

    let mut mds = vec![vec![F::zero(); RATE + 1]; RATE + 1];
    for _ in 0..skip_matrices {
        let _ = lfsr.get_field_elements_mod_p::<F>(2 * (RATE + 1));
    }

    // a qualifying matrix must satisfy the following requirements
    // - there is no duplication among the elements in x or y
    // - there is no i and j such that x[i] + y[j] = p
    // - the resultant MDS passes all the three tests

    let xs = lfsr.get_field_elements_mod_p::<F>(RATE + 1);
    let ys = lfsr.get_field_elements_mod_p::<F>(RATE + 1);

    for i in 0..(RATE + 1) {
        for j in 0..(RATE + 1) {
            mds[i][j] = (xs[i] + &ys[j]).inverse().unwrap();
        }
    }

    (ark, mds)
}

macro_rules! impl_poseidon_default_parameters_field {
    ($field: ident, $params: ident) => {
        impl<P: $params + PoseidonDefaultParameters> PoseidonDefaultParametersField for $field<P> {
            fn get_default_poseidon_parameters<const RATE: usize>(
                optimized_for_weights: bool,
            ) -> Option<PoseidonParameters<Self, RATE, 1>> {
                get_default_poseidon_parameters_internal::<Self, P, RATE>(optimized_for_weights)
            }
        }
    };
}

impl_poseidon_default_parameters_field!(Fp256, Fp256Parameters);
impl_poseidon_default_parameters_field!(Fp384, Fp384Parameters);
impl_poseidon_default_parameters_field!(Fp768, Fp768Parameters);
