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

use crate::{
    overhead,
    snark::marlin::{
        fiat_shamir::{FiatShamirError, FiatShamirRng},
        params::{get_params, OptimizationType},
    },
    traits::DefaultCapacityAlgebraicSponge,
};
use snarkvm_fields::{FieldParameters, PrimeField, ToConstraintField};
use snarkvm_utilities::{BigInteger, FromBits, ToBits};

use core::marker::PhantomData;
use smallvec::SmallVec;

/// An RNG from any algebraic sponge
#[derive(Clone, Debug)]
pub struct FiatShamirAlgebraicSpongeRng<
    TargetField: PrimeField,
    BaseField: PrimeField,
    S: DefaultCapacityAlgebraicSponge<BaseField, 6>,
> {
    /// The algebraic sponge.
    pub(super) s: S,
    #[doc(hidden)]
    _phantom: PhantomData<(TargetField, BaseField)>,
}

impl<TargetField, BaseField, S> FiatShamirRng<TargetField, BaseField>
    for FiatShamirAlgebraicSpongeRng<TargetField, BaseField, S>
where
    TargetField: PrimeField,
    BaseField: PrimeField,
    S: DefaultCapacityAlgebraicSponge<BaseField, 6>,
{
    type Parameters = S::Parameters;

    fn new() -> Self {
        Self { s: S::new(&S::sample_parameters()), _phantom: PhantomData }
    }

    fn absorb_nonnative_field_elements(&mut self, elems: impl IntoIterator<Item = TargetField>, ty: OptimizationType) {
        Self::push_elements_to_sponge(&mut self.s, elems, ty);
    }

    fn absorb_native_field_elements<T: ToConstraintField<BaseField>>(&mut self, src: &[T]) {
        let mut elems = Vec::<BaseField>::new();
        for elem in src.iter() {
            elems.append(&mut elem.to_field_elements().unwrap());
        }
        self.s.absorb(&elems);
    }

    fn absorb_bytes(&mut self, elems: &[u8]) {
        let capacity = BaseField::size_in_bits() - 1;
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
            .map(|bits| BaseField::from_repr(BaseField::BigInteger::from_bits_be(bits).unwrap()).unwrap())
            .collect::<Vec<BaseField>>();

        self.s.absorb(&elements);
    }

    fn squeeze_nonnative_field_elements(
        &mut self,
        num: usize,
        _: OptimizationType,
    ) -> Result<Vec<TargetField>, FiatShamirError> {
        Ok(Self::get_elements_from_sponge(&mut self.s, num, false))
    }

    fn squeeze_native_field_elements(&mut self, num: usize) -> Result<SmallVec<[BaseField; 10]>, FiatShamirError> {
        Ok(self.s.squeeze(num))
    }

    fn squeeze_short_nonnative_field_elements(&mut self, num: usize) -> Result<Vec<TargetField>, FiatShamirError> {
        Ok(Self::get_elements_from_sponge(&mut self.s, num, true))
    }
}

impl<TargetField: PrimeField, BaseField: PrimeField, S: DefaultCapacityAlgebraicSponge<BaseField, 6>>
    FiatShamirAlgebraicSpongeRng<TargetField, BaseField, S>
{
    /// Compress every two elements if possible. Provides a vector of (limb, num_of_additions), both of which are P::BaseField.
    pub fn compress_elements(src_limbs: &[(BaseField, BaseField)], ty: OptimizationType) -> Vec<BaseField> {
        let capacity = BaseField::size_in_bits() - 1;
        let mut dest_limbs = Vec::<BaseField>::new();

        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), ty);

        let adjustment_factor_lookup_table = {
            let mut table = Vec::<BaseField>::new();

            let mut cur = BaseField::one();
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

            let first_max_bits_per_limb = params.bits_per_limb + overhead!(first.1 + BaseField::one());
            let second_max_bits_per_limb = if let Some(second) = second {
                params.bits_per_limb + overhead!(second.1 + BaseField::one())
            } else {
                0
            };

            if let Some(second) = second {
                if first_max_bits_per_limb + second_max_bits_per_limb <= capacity {
                    let adjustment_factor = &adjustment_factor_lookup_table[second_max_bits_per_limb];

                    dest_limbs.push(first.0 * adjustment_factor + second.0);
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

    /// Convert a `TargetField` element into limbs (not constraints)
    /// This is an internal function that would be reused by a number of other functions
    pub fn get_limbs_representations(
        elem: &TargetField,
        optimization_type: OptimizationType,
    ) -> Result<Vec<BaseField>, FiatShamirError> {
        Self::get_limbs_representations_from_big_integer(&elem.to_repr(), optimization_type)
    }

    /// Obtain the limbs directly from a big int
    pub fn get_limbs_representations_from_big_integer(
        elem: &<TargetField as PrimeField>::BigInteger,
        optimization_type: OptimizationType,
    ) -> Result<Vec<BaseField>, FiatShamirError> {
        let params = get_params(TargetField::size_in_bits(), BaseField::size_in_bits(), optimization_type);

        // Push the lower limbs first
        let mut limbs: Vec<BaseField> = Vec::new();
        let mut cur = *elem;
        for _ in 0..params.num_limbs {
            let cur_bits = cur.to_bits_be(); // `to_bits` is big endian
            let cur_mod_r = <BaseField as PrimeField>::BigInteger::from_bits_be(
                &cur_bits[cur_bits.len() - params.bits_per_limb..],
            )?; // therefore, the lowest `bits_per_non_top_limb` bits is what we want.
            limbs.push(BaseField::from_repr(cur_mod_r).unwrap());
            cur.divn(params.bits_per_limb as u32);
        }

        // then we reserve, so that the limbs are ``big limb first''
        limbs.reverse();

        Ok(limbs)
    }

    /// Push elements to sponge, treated in the non-native field representations.
    pub fn push_elements_to_sponge(sponge: &mut S, src: impl IntoIterator<Item = TargetField>, ty: OptimizationType) {
        let mut src_limbs = Vec::<(BaseField, BaseField)>::new();

        for elem in src {
            let limbs = Self::get_limbs_representations(&elem, ty).unwrap();
            for limb in limbs.iter() {
                src_limbs.push((*limb, BaseField::one()));
                // specifically set to one, since most gadgets in the constraint world would not have zero noise (due to the relatively weak normal form testing in `alloc`)
            }
        }

        let dest_limbs = Self::compress_elements(&src_limbs, ty);
        sponge.absorb(&dest_limbs);
    }

    /// obtain random bits from hashchain.
    /// not guaranteed to be uniformly distributed, should only be used in certain situations.
    pub fn get_bits_from_sponge(sponge: &mut S, num_bits: usize) -> Vec<bool> {
        let bits_per_element = BaseField::size_in_bits() - 1;
        let num_elements = (num_bits + bits_per_element - 1) / bits_per_element;

        let src_elements = sponge.squeeze(num_elements);
        let mut dest_bits = Vec::<bool>::with_capacity(num_elements * bits_per_element);

        let skip = (BaseField::Parameters::REPR_SHAVE_BITS + 1) as usize;
        for elem in src_elements.iter() {
            // discard the highest bit
            let elem_bits = elem.to_repr().to_bits_be();
            dest_bits.extend_from_slice(&elem_bits[skip..]);
        }
        dest_bits.truncate(num_bits);

        dest_bits
    }

    /// obtain random elements from hashchain.
    /// not guaranteed to be uniformly distributed, should only be used in certain situations.
    pub fn get_elements_from_sponge(
        sponge: &mut S,
        num_elements: usize,
        outputs_short_elements: bool,
    ) -> Vec<TargetField> {
        let num_bits_per_nonnative = if outputs_short_elements {
            168
        } else {
            TargetField::size_in_bits() - 1 // also omit the highest bit
        };
        let bits = Self::get_bits_from_sponge(sponge, num_bits_per_nonnative * num_elements);

        let mut lookup_table = Vec::<TargetField>::new();
        let mut cur = TargetField::one();
        for _ in 0..num_bits_per_nonnative {
            lookup_table.push(cur);
            cur.double_in_place();
        }

        let dest_elements = bits
            .chunks_exact(num_bits_per_nonnative)
            .map(|per_nonnative_bits| {
                // technically, this can be done via BigInterger::from_bits; here, we use this method for consistency with the gadget counterpart
                let mut res = TargetField::zero();

                for (i, bit) in per_nonnative_bits.iter().rev().enumerate() {
                    if *bit {
                        res += &lookup_table[i];
                    }
                }
                res
            })
            .collect::<Vec<_>>();
        debug_assert_eq!(dest_elements.len(), num_elements);

        dest_elements
    }
}
