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

use crate::snark::marlin::{fiat_shamir::FiatShamirRng, params::OptimizationType, FiatShamirError};
use rand::RngCore;
use snarkvm_fields::{PrimeField, ToConstraintField};

use core::{fmt::Debug, marker::PhantomData};
use digest::Digest;
use rand_chacha::ChaChaRng;
use rand_core::SeedableRng;
use smallvec::SmallVec;

/// Implements a Fiat-Shamir based Rng that allows one to incrementally update
/// the seed based on new messages in the proof transcript.
/// Use a ChaCha stream cipher to generate the actual pseudorandom bits.
/// Use a digest function to do absorbing.
#[derive(Clone, Debug)]
pub struct FiatShamirChaChaRng<TargetField: PrimeField, BaseField: PrimeField, D: Digest + Clone + Debug> {
    /// The ChaCha RNG.
    r: Option<ChaChaRng>,
    /// The initial seed for the RNG.
    seed: Option<Vec<u8>>,
    #[doc(hidden)]
    _phantom: PhantomData<(TargetField, BaseField, D)>,
}

impl<TargetField: PrimeField, BaseField: PrimeField, D: Digest + Clone + Debug> FiatShamirRng<TargetField, BaseField>
    for FiatShamirChaChaRng<TargetField, BaseField, D>
{
    type Parameters = ();

    fn new() -> Self {
        Self { r: None, seed: None, _phantom: PhantomData }
    }

    fn absorb_nonnative_field_elements(&mut self, elems: impl IntoIterator<Item = TargetField>, _: OptimizationType) {
        let mut bytes = Vec::new();
        for elem in elems {
            elem.write_le(&mut bytes).expect("failed to convert to bytes");
        }
        self.absorb_bytes(&bytes);
    }

    fn absorb_native_field_elements<T: ToConstraintField<BaseField>>(&mut self, src: &[T]) {
        let mut elems = Vec::<BaseField>::new();
        for elem in src.iter() {
            elems.append(&mut elem.to_field_elements().unwrap());
        }

        let mut bytes = Vec::new();
        for elem in elems.iter() {
            elem.write_le(&mut bytes).expect("failed to convert to bytes");
        }
        self.absorb_bytes(&bytes);
    }

    fn absorb_bytes(&mut self, elements: &[u8]) {
        let mut bytes = elements.to_vec();
        // If a seed exists, extend the byte vector to include the existing seed.
        if let Some(seed) = &self.seed {
            bytes.extend_from_slice(seed);
        }

        let new_seed = (*D::digest(&bytes).as_slice()).to_vec();
        self.seed = Some(new_seed.to_vec());

        let mut seed = [0u8; 32];
        for (i, byte) in new_seed.as_slice().iter().enumerate() {
            seed[i] = *byte;
        }

        self.r = Some(ChaChaRng::from_seed(seed));
    }

    fn squeeze_nonnative_field_elements(
        &mut self,
        num: usize,
        _: OptimizationType,
    ) -> Result<Vec<TargetField>, FiatShamirError> {
        // Ensure the RNG is initialized.
        let rng = match &mut self.r {
            Some(rng) => rng,
            None => return Err(FiatShamirError::UninitializedRNG),
        };

        let mut res = Vec::<TargetField>::new();
        for _ in 0..num {
            res.push(TargetField::rand(rng));
        }
        Ok(res)
    }

    fn squeeze_native_field_elements(&mut self, num: usize) -> Result<SmallVec<[BaseField; 10]>, FiatShamirError> {
        // Ensure the RNG is initialized.
        let rng = match &mut self.r {
            Some(rng) => rng,
            None => return Err(FiatShamirError::UninitializedRNG),
        };

        let mut res = SmallVec::with_capacity(num);
        for _ in 0..num {
            res.push(BaseField::rand(rng));
        }
        Ok(res)
    }

    fn squeeze_short_nonnative_field_elements(&mut self, num: usize) -> Result<Vec<TargetField>, FiatShamirError> {
        // Ensure the RNG is initialized.
        let rng = match &mut self.r {
            Some(rng) => rng,
            None => return Err(FiatShamirError::UninitializedRNG),
        };

        let mut res = Vec::<TargetField>::new();
        for _ in 0..num {
            let mut x = [0u8; 21];
            rng.fill_bytes(&mut x);
            res.push(TargetField::from_random_bytes(&x).unwrap());
        }
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use snarkvm_curves::bls12_377::{Fq, Fr};
    use snarkvm_utilities::rand::Uniform;

    use blake2::Blake2s256;
    use rand_chacha::ChaChaRng;

    const NUM_ABSORBED_RAND_FIELD_ELEMS: usize = 10;
    const NUM_ABSORBED_RAND_BYTE_ELEMS: usize = 10;
    const SIZE_ABSORBED_BYTE_ELEM: usize = 64;

    const NUM_SQUEEZED_FIELD_ELEMS: usize = 10;
    const NUM_SQUEEZED_SHORT_FIELD_ELEMS: usize = 10;

    #[test]
    fn test_chacharng() {
        let mut rng = ChaChaRng::seed_from_u64(123456789u64);

        let mut absorbed_rand_field_elems = Vec::new();
        for _ in 0..NUM_ABSORBED_RAND_FIELD_ELEMS {
            absorbed_rand_field_elems.push(Fr::rand(&mut rng));
        }

        let mut absorbed_rand_byte_elems = Vec::<Vec<u8>>::new();
        for _ in 0..NUM_ABSORBED_RAND_BYTE_ELEMS {
            absorbed_rand_byte_elems.push((0..SIZE_ABSORBED_BYTE_ELEM).map(|_| u8::rand(&mut rng)).collect());
        }

        let mut fs_rng = FiatShamirChaChaRng::<Fr, Fq, Blake2s256>::new();
        fs_rng.absorb_nonnative_field_elements(absorbed_rand_field_elems.clone(), OptimizationType::Weight);
        for absorbed_rand_byte_elem in absorbed_rand_byte_elems {
            fs_rng.absorb_bytes(&absorbed_rand_byte_elem);
        }

        let _squeezed_fields_elems =
            fs_rng.squeeze_nonnative_field_elements(NUM_SQUEEZED_FIELD_ELEMS, OptimizationType::Weight);
        let _squeezed_short_fields_elems =
            fs_rng.squeeze_short_nonnative_field_elements(NUM_SQUEEZED_SHORT_FIELD_ELEMS);
    }
}
