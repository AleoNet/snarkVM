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

use snarkvm_curves::traits::ProjectiveCurve;
use snarkvm_fields::{FieldParameters, PrimeField};
use snarkvm_utilities::{cfg_into_iter, cfg_iter, cfg_iter_mut, ToBits};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub struct FixedBase;

impl FixedBase {
    pub fn get_mul_window_size(num_scalars: usize) -> usize {
        match num_scalars < 32 {
            true => 3,
            false => super::ln_without_floats(num_scalars),
        }
    }

    pub fn get_window_table<T: ProjectiveCurve>(scalar_size: usize, window: usize, g: T) -> Vec<Vec<T>> {
        let in_window = 1 << window;
        let outerc = (scalar_size + window - 1) / window;
        let last_in_window = 1 << (scalar_size - (outerc - 1) * window);

        let mut multiples_of_g = vec![vec![T::zero(); in_window]; outerc];

        let mut g_outer = g;
        let mut g_outers = Vec::with_capacity(outerc);
        for _ in 0..outerc {
            g_outers.push(g_outer);
            for _ in 0..window {
                g_outer.double_in_place();
            }
        }

        cfg_iter_mut!(multiples_of_g).enumerate().take(outerc).zip(g_outers).for_each(
            |((outer, multiples_of_g), g_outer)| {
                let cur_in_window = if outer == outerc - 1 { last_in_window } else { in_window };

                let mut g_inner = T::zero();
                for inner in multiples_of_g.iter_mut().take(cur_in_window) {
                    *inner = g_inner;
                    g_inner += &g_outer;
                }
            },
        );
        multiples_of_g
    }

    pub fn windowed_mul<T: ProjectiveCurve>(
        outerc: usize,
        window: usize,
        multiples_of_g: &[Vec<T>],
        scalar: &T::ScalarField,
    ) -> T {
        let scalar_val = scalar.to_repr().to_bits_le();

        cfg_into_iter!(0..outerc)
            .map(|outer| {
                let mut inner = 0usize;
                for i in 0..window {
                    if outer * window + i < (<T::ScalarField as PrimeField>::Parameters::MODULUS_BITS as usize)
                        && scalar_val[outer * window + i]
                    {
                        inner |= 1 << i;
                    }
                }
                multiples_of_g[outer][inner]
            })
            .sum::<T>()
            + multiples_of_g[0][0]
    }

    pub fn msm<T: ProjectiveCurve>(
        scalar_size: usize,
        window: usize,
        table: &[Vec<T>],
        v: &[T::ScalarField],
    ) -> Vec<T> {
        let outerc = (scalar_size + window - 1) / window;
        assert!(outerc <= table.len());

        cfg_iter!(v).map(|e| Self::windowed_mul::<T>(outerc, window, table, e)).collect::<Vec<_>>()
    }
}
