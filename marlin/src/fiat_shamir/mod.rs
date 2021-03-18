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

use snarkvm_fields::{FieldParameters, PrimeField, ToConstraintField};
use snarkvm_nonnative::{
    params::{get_params, OptimizationType},
    AllocatedNonNativeFieldVar,
};
use snarkvm_utilities::BigInteger;

use digest::Digest;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use std::marker::PhantomData;

/// The constraints for Fiat-Shamir
pub mod constraints;
/// The Poseidon sponge
pub mod poseidon;

/// a macro for computing ceil(log2(x))+1 for a field element x
#[doc(hidden)]
#[macro_export]
macro_rules! overhead {
    ($x:expr) => {{
        use snarkvm_utilities::BigInteger;
        let num = $x;
        let num_bits = num.into_repr().to_bits_be();
        let mut skipped_bits = 0;
        for b in num_bits.iter() {
            if *b == false {
                skipped_bits += 1;
            } else {
                break;
            }
        }

        let mut is_power_of_2 = true;
        for b in num_bits.iter().skip(skipped_bits + 1) {
            if *b == true {
                is_power_of_2 = false;
            }
        }

        if is_power_of_2 {
            num_bits.len() - skipped_bits
        } else {
            num_bits.len() - skipped_bits + 1
        }
    }};
}

/// the trait for Fiat-Shamir RNG
pub trait FiatShamirRng<F: PrimeField, CF: PrimeField>: RngCore {
    /// initialize the RNG
    fn new() -> Self;

    /// take in field elements
    fn absorb_nonnative_field_elements(&mut self, elems: &[F], ty: OptimizationType);
    /// take in field elements
    fn absorb_native_field_elements<T: ToConstraintField<CF>>(&mut self, elems: &[T]);
    /// take in bytes
    fn absorb_bytes(&mut self, elems: &[u8]);

    /// take out field elements
    fn squeeze_nonnative_field_elements(&mut self, num: usize, ty: OptimizationType) -> Vec<F>;
    /// take in field elements
    fn squeeze_native_field_elements(&mut self, num: usize) -> Vec<CF>;
    /// take out field elements of 128 bits
    fn squeeze_128_bits_nonnative_field_elements(&mut self, num: usize) -> Vec<F>;
}

/// the trait for algebraic sponge
pub trait AlgebraicSponge<CF: PrimeField>: Clone {
    /// initialize the sponge
    fn new() -> Self;
    /// take in field elements
    fn absorb(&mut self, elems: &[CF]);
    /// take out field elements
    fn squeeze(&mut self, num: usize) -> Vec<CF>;
}

/// use a ChaCha stream cipher to generate the actual pseudorandom bits
/// use a digest funcion to do absorbing
pub struct FiatShamirChaChaRng<F: PrimeField, CF: PrimeField, D: Digest> {
    /// ChachaRng.
    pub r: ChaChaRng,
    /// Seed used for randomness.
    pub seed: Vec<u8>,
    #[doc(hidden)]
    field: PhantomData<F>,
    representation_field: PhantomData<CF>,
    digest: PhantomData<D>,
}

impl<F: PrimeField, CF: PrimeField, D: Digest> RngCore for FiatShamirChaChaRng<F, CF, D> {
    fn next_u32(&mut self) -> u32 {
        self.r.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.r.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.r.fill_bytes(dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
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
            field: PhantomData,
            representation_field: PhantomData,
            digest: PhantomData,
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

/// rng from any algebraic sponge
pub struct FiatShamirAlgebraicSpongeRng<F: PrimeField, CF: PrimeField, S: AlgebraicSponge<CF>> {
    /// Algebraic sponge.
    pub s: S,
    #[doc(hidden)]
    f_phantom: PhantomData<F>,
    cf_phantom: PhantomData<CF>,
}

impl<F: PrimeField, CF: PrimeField, S: AlgebraicSponge<CF>> FiatShamirAlgebraicSpongeRng<F, CF, S> {
    /// compress every two elements if possible. Provides a vector of (limb, num_of_additions), both of which are P::BaseField.
    pub fn compress_elements(src_limbs: &[(CF, CF)], ty: OptimizationType) -> Vec<CF> {
        let capacity = CF::size_in_bits() - 1;
        let mut dest_limbs = Vec::<CF>::new();

        let params = get_params(F::size_in_bits(), CF::size_in_bits(), ty);

        let adjustment_factor_lookup_table = {
            let mut table = Vec::<CF>::new();

            let mut cur = CF::one();
            for _ in 1..=capacity {
                table.push(cur);
                cur.double_in_place();
            }

            table
        };

        let mut i = 0;
        let src_len = src_limbs.len();
        while i < src_len {
            let first = &src_limbs[i];
            let second = if i + 1 < src_len { Some(&src_limbs[i + 1]) } else { None };

            let first_max_bits_per_limb = params.bits_per_limb + overhead!(first.1 + &CF::one());
            let second_max_bits_per_limb = if let Some(second) = second {
                params.bits_per_limb + overhead!(second.1 + &CF::one())
            } else {
                0
            };

            if let Some(second) = second {
                if first_max_bits_per_limb + second_max_bits_per_limb <= capacity {
                    let adjustment_factor = &adjustment_factor_lookup_table[second_max_bits_per_limb];

                    dest_limbs.push(first.0 * adjustment_factor + &second.0);
                    i += 2;
                } else {
                    dest_limbs.push(first.0);
                    i += 1;
                }
            } else {
                dest_limbs.push(first.0);
                i += 1;
            }
        }

        dest_limbs
    }

    /// push elements to sponge, treated in the non-native field representations.
    pub fn push_elements_to_sponge(sponge: &mut S, src: &[F], ty: OptimizationType) {
        let mut src_limbs = Vec::<(CF, CF)>::new();

        for elem in src.iter() {
            let limbs = AllocatedNonNativeFieldVar::<F, CF>::get_limbs_representations(elem, ty).unwrap();
            for limb in limbs.iter() {
                src_limbs.push((*limb, CF::one()));
                // specifically set to one, since most gadgets in the constraint world would not have zero noise (due to the relatively weak normal form testing in `alloc`)
            }
        }

        let dest_limbs = Self::compress_elements(&src_limbs, ty);
        sponge.absorb(&dest_limbs);
    }

    /// obtain random bits from hashchain.
    /// not guaranteed to be uniformly distributed, should only be used in certain situations.
    pub fn get_bits_from_sponge(sponge: &mut S, num_bits: usize) -> Vec<bool> {
        let bits_per_element = CF::size_in_bits() - 1;
        let num_elements = (num_bits + bits_per_element - 1) / bits_per_element;

        let src_elements = sponge.squeeze(num_elements);
        let mut dest_bits = Vec::<bool>::new();

        let skip = (CF::Parameters::REPR_SHAVE_BITS + 1) as usize;
        for elem in src_elements.iter() {
            // discard the highest bit
            let elem_bits = elem.into_repr().to_bits_be();
            dest_bits.extend_from_slice(&elem_bits[skip..]);
        }

        dest_bits
    }

    /// obtain random elements from hashchain.
    /// not guaranteed to be uniformly distributed, should only be used in certain situations.
    pub fn get_elements_from_sponge(sponge: &mut S, num_elements: usize, outputs_short_elements: bool) -> Vec<F> {
        let num_bits_per_nonnative = if outputs_short_elements {
            128
        } else {
            F::size_in_bits() - 1 // also omit the highest bit
        };
        let bits = Self::get_bits_from_sponge(sponge, num_bits_per_nonnative * num_elements);

        let mut lookup_table = Vec::<F>::new();
        let mut cur = F::one();
        for _ in 0..num_bits_per_nonnative {
            lookup_table.push(cur);
            cur.double_in_place();
        }

        let mut dest_elements = Vec::<F>::new();
        bits.chunks_exact(num_bits_per_nonnative)
            .for_each(|per_nonnative_bits| {
                // technically, this can be done via BigInteger::from_bits; here, we use this method for consistency with the gadget counterpart
                let mut res = F::zero();

                for (i, bit) in per_nonnative_bits.iter().rev().enumerate() {
                    if *bit {
                        res += &lookup_table[i];
                    }
                }

                dest_elements.push(res);
            });

        dest_elements
    }
}

impl<F: PrimeField, CF: PrimeField, S: AlgebraicSponge<CF>> RngCore for FiatShamirAlgebraicSpongeRng<F, CF, S> {
    fn next_u32(&mut self) -> u32 {
        assert!(
            CF::size_in_bits() > 128,
            "The native field of the algebraic sponge is too small."
        );

        let mut dest = [0u8; 4];
        self.fill_bytes(&mut dest);

        u32::from_be_bytes(dest)
    }

    fn next_u64(&mut self) -> u64 {
        assert!(
            CF::size_in_bits() > 128,
            "The native field of the algebraic sponge is too small."
        );

        let mut dest = [0u8; 8];
        self.fill_bytes(&mut dest);

        u64::from_be_bytes(dest)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        assert!(
            CF::size_in_bits() > 128,
            "The native field of the algebraic sponge is too small."
        );

        let capacity = CF::size_in_bits() - 128;
        let len = dest.len() * 8;

        let num_of_elements = (capacity + len - 1) / len;
        let elements = self.s.squeeze(num_of_elements);

        let mut bits = Vec::<bool>::new();
        for elem in elements.iter() {
            let mut elem_bits = elem.into_repr().to_bits_be();
            elem_bits.reverse();
            bits.extend_from_slice(&elem_bits[0..capacity]);
        }

        bits.truncate(len);
        bits.chunks_exact(8).enumerate().for_each(|(i, bits_per_byte)| {
            let mut byte = 0;
            for (j, bit) in bits_per_byte.iter().enumerate() {
                if *bit {
                    byte += 1 << j;
                }
            }
            dest[i] = byte;
        });
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        assert!(
            CF::size_in_bits() > 128,
            "The native field of the algebraic sponge is too small."
        );

        self.fill_bytes(dest);
        Ok(())
    }
}

impl<F: PrimeField, CF: PrimeField, S: AlgebraicSponge<CF>> FiatShamirRng<F, CF>
    for FiatShamirAlgebraicSpongeRng<F, CF, S>
{
    fn new() -> Self {
        Self {
            s: S::new(),
            f_phantom: PhantomData,
            cf_phantom: PhantomData,
        }
    }

    fn absorb_nonnative_field_elements(&mut self, elems: &[F], ty: OptimizationType) {
        Self::push_elements_to_sponge(&mut self.s, elems, ty);
    }

    fn absorb_native_field_elements<T: ToConstraintField<CF>>(&mut self, src: &[T]) {
        let mut elems = Vec::<CF>::new();
        for elem in src.iter() {
            elems.append(&mut elem.to_field_elements().unwrap());
        }
        self.s.absorb(&elems);
    }

    fn absorb_bytes(&mut self, elems: &[u8]) {
        let capacity = CF::size_in_bits() - 1;
        let mut bits = Vec::<bool>::new();
        for elem in elems.iter() {
            bits.append(&mut vec![
                elem & 128 != 0,
                elem & 64 != 0,
                elem & 32 != 0,
                elem & 16 != 0,
                elem & 8 != 0,
                elem & 4 != 0,
                elem & 2 != 0,
                elem & 1 != 0,
            ]);
        }
        let elements = bits
            .chunks(capacity)
            .map(|bits| CF::from_repr(CF::BigInteger::from_bits_be(bits.to_vec())).unwrap())
            .collect::<Vec<CF>>();

        self.s.absorb(&elements);
    }

    fn squeeze_nonnative_field_elements(&mut self, num: usize, _: OptimizationType) -> Vec<F> {
        Self::get_elements_from_sponge(&mut self.s, num, false)
    }

    fn squeeze_native_field_elements(&mut self, num: usize) -> Vec<CF> {
        self.s.squeeze(num)
    }

    fn squeeze_128_bits_nonnative_field_elements(&mut self, num: usize) -> Vec<F> {
        Self::get_elements_from_sponge(&mut self.s, num, true)
    }
}
