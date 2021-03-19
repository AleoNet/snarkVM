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

use crate::{rng::FiatShamirRng, PhantomData};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_nonnative::params::OptimizationType;

use digest::Digest;
use rand_chacha::ChaChaRng;
use rand_core::{Error, RngCore, SeedableRng};

/// Implements a Fiat-Shamir based Rng that allows one to incrementally update
/// the seed based on new messages in the proof transcript.
/// Use a ChaCha stream cipher to generate the actual pseudorandom bits.
/// Use a digest function to do absorbing.
pub struct FiatShamirChaChaRng<TargetField: PrimeField, BaseField: PrimeField, D: Digest> {
    /// The ChaCha RNG.
    pub r: ChaChaRng,
    /// The initial seed for the RNG.
    pub seed: Vec<u8>,
    #[doc(hidden)]
    _target_field: PhantomData<TargetField>,
    #[doc(hidden)]
    _base_field: PhantomData<BaseField>,
    #[doc(hidden)]
    _digest: PhantomData<D>,
}

impl<TargetField: PrimeField, BaseField: PrimeField, D: Digest> RngCore
    for FiatShamirChaChaRng<TargetField, BaseField, D>
{
    fn next_u32(&mut self) -> u32 {
        self.r.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.r.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.r.fill_bytes(dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.r.try_fill_bytes(dest)
    }
}

impl<F: PrimeField, CF: PrimeField, D: Digest> FiatShamirRng<F, CF> for FiatShamirChaChaRng<F, CF, D> {
    fn new() -> Self {
        let seed = [0; 32];
        let r = ChaChaRng::from_seed(seed);
        Self {
            r,
            seed: seed.to_vec(),
            _target_field: PhantomData,
            _base_field: PhantomData,
            _digest: PhantomData,
        }
    }

    fn absorb_nonnative_field_elements(&mut self, elems: &[F], _: OptimizationType) {
        let mut bytes = Vec::new();
        for elem in elems {
            elem.write(&mut bytes).expect("failed to convert to bytes");
        }
        self.absorb_bytes(&bytes);
    }

    fn absorb_native_field_elements<T: ToConstraintField<CF>>(&mut self, src: &[T]) {
        let mut elems = Vec::<CF>::new();
        for elem in src.iter() {
            elems.append(&mut elem.to_field_elements().unwrap());
        }

        let mut bytes = Vec::new();
        for elem in elems.iter() {
            elem.write(&mut bytes).expect("failed to convert to bytes");
        }
        self.absorb_bytes(&bytes);
    }

    fn absorb_bytes(&mut self, elems: &[u8]) {
        let mut bytes = elems.to_vec();
        bytes.extend_from_slice(&self.seed);

        let new_seed = D::digest(&bytes);
        self.seed = (*new_seed.as_slice()).to_vec();

        let mut seed = [0u8; 32];
        for (i, byte) in self.seed.as_slice().iter().enumerate() {
            seed[i] = *byte;
        }

        self.r = ChaChaRng::from_seed(seed);
    }

    fn squeeze_nonnative_field_elements(&mut self, num: usize, _: OptimizationType) -> Vec<F> {
        let mut res = Vec::<F>::new();
        for _ in 0..num {
            res.push(F::rand(&mut self.r));
        }
        res
    }

    fn squeeze_native_field_elements(&mut self, num: usize) -> Vec<CF> {
        let mut res = Vec::<CF>::new();
        for _ in 0..num {
            res.push(CF::rand(&mut self.r));
        }
        res
    }

    fn squeeze_128_bits_nonnative_field_elements(&mut self, num: usize) -> Vec<F> {
        let mut res = Vec::<F>::new();
        for _ in 0..num {
            let mut x = [0u8; 16];
            self.r.fill_bytes(&mut x);
            res.push(F::from_random_bytes(&x).unwrap());
        }
        res
    }
}
