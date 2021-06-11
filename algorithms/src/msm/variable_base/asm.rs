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

use std::any::TypeId;

use snarkvm_curves::{bls12_377::G1Affine, traits::AffineCurve};
use snarkvm_fields::{Field, FieldParameters, PrimeField, Zero};

#[link(name = "blst377", kind = "static")]
extern "C" {
    fn msm_pippenger_6(
        result: *mut u64,
        bases_in: *const u8,
        scalars_in: *const u8,
        num_pairs: usize,
        scalar_bits: usize,
        c: usize,
    );
}

pub fn msm_asm<G: AffineCurve>(bases: &[G], scalars: &[<G::ScalarField as Field>::BigInteger]) -> G::Projective {
    if TypeId::of::<G>() != TypeId::of::<G1Affine>() {
        unimplemented!("trying to use asm for unsupported curve");
    }

    if scalars.len() < 4 {
        let mut acc = G::Projective::zero();

        for (base, scalar) in bases.iter().zip(scalars.iter()) {
            acc += &base.mul(*scalar);
        }
        return acc;
    }

    let c = if scalars.len() < 32 {
        3
    } else {
        (2.0 / 3.0 * (f64::from(scalars.len() as u32)).log2() + 2.0).ceil() as usize
    };
    let num_bits = <G::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize;

    let mut sn_result = G::Projective::zero();

    unsafe {
        let bases_raw = &*(bases.as_ptr() as *const u8);
        let scalars_raw = &*(scalars.as_ptr() as *const u8);
        #[allow(trivial_casts)]
        let sn_result_raw = std::slice::from_raw_parts_mut(&mut sn_result as *mut _ as *mut u64, 18);
        msm_pippenger_6(
            sn_result_raw.as_mut_ptr(),
            bases_raw,
            scalars_raw,
            scalars.len(),
            num_bits,
            c,
        );
    }
    sn_result
}
