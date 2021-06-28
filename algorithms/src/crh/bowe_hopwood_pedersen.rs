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

pub use crate::crh::pedersen_parameters::PedersenSize;

use super::bowe_hopwood_pedersen_parameters::*;
use crate::{
    crh::{PedersenCRH, PedersenCRHParameters},
    errors::CRHError,
    traits::CRH,
};
use snarkvm_curves::Group;
use snarkvm_fields::{ConstraintFieldError, Field, PrimeField, ToConstraintField};
use snarkvm_utilities::biginteger::biginteger::BigInteger;

use bitvec::{order::Lsb0, view::BitView};
use rand::Rng;

// we cant use these in array sizes since they are from a trait (and cant be refered to at const time)
const MAX_WINDOW_SIZE: usize = 256;
const MAX_NUM_WINDOWS: usize = 296;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoweHopwoodPedersenCRH<G: Group, S: PedersenSize> {
    pub parameters: PedersenCRHParameters<G, S>,
    pub bowe_hopwood_parameters: BoweHopwoodPedersenCRHParameters<G>,
}

impl<G: Group, S: PedersenSize> BoweHopwoodPedersenCRH<G, S> {
    pub fn create_generators<R: Rng>(rng: &mut R) -> Vec<Vec<G>> {
        let mut generators = Vec::with_capacity(S::NUM_WINDOWS);
        for _ in 0..S::NUM_WINDOWS {
            let mut generators_for_segment = Vec::with_capacity(S::WINDOW_SIZE);
            let mut base = G::rand(rng);
            for _ in 0..S::WINDOW_SIZE {
                generators_for_segment.push(base);
                for _ in 0..4 {
                    base.double_in_place();
                }
            }
            generators.push(generators_for_segment);
        }
        generators
    }
}

impl<G: Group, S: PedersenSize> CRH for BoweHopwoodPedersenCRH<G, S> {
    type Output = G;
    type Parameters = PedersenCRHParameters<G, S>;

    const INPUT_SIZE_BITS: usize = PedersenCRH::<G, S>::INPUT_SIZE_BITS;

    fn setup<R: Rng>(rng: &mut R) -> Self {
        fn calculate_num_chunks_in_segment<F: PrimeField>() -> usize {
            let upper_limit = F::modulus_minus_one_div_two();
            let mut c = 0;
            let mut range = F::BigInteger::from(2_u64);
            while range < upper_limit {
                range.muln(4);
                c += 1;
            }

            c
        }

        let maximum_num_chunks_in_segment = calculate_num_chunks_in_segment::<G::ScalarField>();
        if S::WINDOW_SIZE > maximum_num_chunks_in_segment {
            panic!(
                "Bowe-Hopwood hash must have a window size resulting in scalars < (p-1)/2, \
                 maximum segment size is {}",
                maximum_num_chunks_in_segment
            );
        }

        let time = start_timer!(|| format!(
            "BoweHopwoodPedersenCRH::Setup: {} segments of {} 3-bit chunks; {{0,1}}^{{{}}} -> G",
            S::NUM_WINDOWS,
            S::WINDOW_SIZE,
            S::WINDOW_SIZE * S::NUM_WINDOWS * BOWE_HOPWOOD_CHUNK_SIZE
        ));
        let bases = Self::create_generators(rng);
        end_timer!(time);

        let parameters = Self::Parameters::from(bases);

        let bowe_hopwood_parameters = BoweHopwoodPedersenCRHParameters::new();

        Self {
            parameters,
            bowe_hopwood_parameters,
        }
    }

    fn hash(&self, input: &[u8]) -> Result<Self::Output, CRHError> {
        let eval_time = start_timer!(|| "BoweHopwoodPedersenCRH::Eval");

        if (input.len() * 8) > S::WINDOW_SIZE * S::NUM_WINDOWS {
            return Err(CRHError::IncorrectInputLength(
                input.len(),
                S::WINDOW_SIZE,
                S::NUM_WINDOWS,
            ));
        }
        assert!(S::WINDOW_SIZE <= MAX_WINDOW_SIZE);
        assert!(S::NUM_WINDOWS <= MAX_NUM_WINDOWS);

        // overzealous but stack allocation
        let mut buffer = [0u8; MAX_WINDOW_SIZE * MAX_NUM_WINDOWS / 8 + BOWE_HOPWOOD_CHUNK_SIZE + 1];
        buffer[..input.len()].copy_from_slice(input);
        let buf_slice = (&buffer[..]).view_bits::<Lsb0>();

        let mut bit_len = S::WINDOW_SIZE * S::NUM_WINDOWS;
        if bit_len % BOWE_HOPWOOD_CHUNK_SIZE != 0 {
            bit_len += BOWE_HOPWOOD_CHUNK_SIZE - (bit_len % BOWE_HOPWOOD_CHUNK_SIZE);
        }

        assert_eq!(bit_len % BOWE_HOPWOOD_CHUNK_SIZE, 0);

        assert_eq!(
            self.parameters.bases.len(),
            S::NUM_WINDOWS,
            "Incorrect pp of size {:?} for window params {:?}x{:?}x{}",
            self.parameters.bases.len(),
            S::WINDOW_SIZE,
            S::NUM_WINDOWS,
            BOWE_HOPWOOD_CHUNK_SIZE,
        );
        assert_eq!(self.parameters.bases.len(), S::NUM_WINDOWS);
        for bases in self.parameters.bases.iter() {
            assert_eq!(bases.len(), S::WINDOW_SIZE);
        }
        let base_lookup = self.bowe_hopwood_parameters.base_lookup(&self.parameters);
        assert_eq!(base_lookup.len(), S::NUM_WINDOWS);
        for bases in base_lookup.iter() {
            assert_eq!(bases.len(), S::WINDOW_SIZE);
        }
        assert_eq!(BOWE_HOPWOOD_CHUNK_SIZE, 3);

        // Compute sum of h_i^{sum of
        // (1-2*c_{i,j,2})*(1+c_{i,j,0}+2*c_{i,j,1})*2^{4*(j-1)} for all j in segment}
        // for all i. Described in section 5.4.1.7 in the Zcash protocol
        // specification.
        let result = buf_slice[..bit_len]
            .chunks(S::WINDOW_SIZE * BOWE_HOPWOOD_CHUNK_SIZE)
            .zip(base_lookup)
            .map(|(segment_bits, segment_generators)| {
                segment_bits
                    .chunks(BOWE_HOPWOOD_CHUNK_SIZE)
                    .zip(segment_generators)
                    .map(|(chunk_bits, generator)| {
                        &generator
                            [(chunk_bits[0] as usize) | (chunk_bits[1] as usize) << 1 | (chunk_bits[2] as usize) << 2]
                    })
                    .fold(G::zero(), |a, b| a + b)
            })
            .fold(G::zero(), |a, b| a + b);

        end_timer!(eval_time);

        Ok(result)
    }

    fn parameters(&self) -> &Self::Parameters {
        &self.parameters
    }
}

impl<G: Group, S: PedersenSize> From<PedersenCRHParameters<G, S>> for BoweHopwoodPedersenCRH<G, S> {
    fn from(parameters: PedersenCRHParameters<G, S>) -> Self {
        Self {
            bowe_hopwood_parameters: BoweHopwoodPedersenCRHParameters::new(),
            parameters,
        }
    }
}

impl<F: Field, G: Group + ToConstraintField<F>, S: PedersenSize> ToConstraintField<F> for BoweHopwoodPedersenCRH<G, S> {
    #[inline]
    fn to_field_elements(&self) -> Result<Vec<F>, ConstraintFieldError> {
        self.parameters.to_field_elements()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use snarkvm_curves::edwards_bls12::EdwardsProjective;

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct CRHSize;

    impl PedersenSize for CRHSize {
        const NUM_WINDOWS: usize = 8;
        const WINDOW_SIZE: usize = 32;
    }

    #[test]
    fn test_bowe_pedersen() {
        let mut rng = rand_xorshift::XorShiftRng::seed_from_u64(23453245);
        let parameters = <BoweHopwoodPedersenCRH<EdwardsProjective, CRHSize> as CRH>::setup(&mut rng);
        let input = vec![127u8; 32];

        let output = <BoweHopwoodPedersenCRH<EdwardsProjective, CRHSize> as CRH>::hash(&parameters, &input).unwrap();
        assert_eq!(
            &*output.to_string(),
            "GroupAffine(x=232405123812771034726439972860096518067116445442313271493943612938654881935, y=752634260468672343124870935373206613671657768711738358314821821547485346646)"
        );
    }
}
