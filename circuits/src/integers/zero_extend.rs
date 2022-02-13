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

use crate::{Boolean, Environment, Mode};

use std::iter;

/// Zero extends an array of bits to the desired length.
/// Expects least significant bit first
pub trait ZeroExtend
where
    Self: std::marker::Sized,
{
    fn zero_extend(bits: &[Self], length: usize) -> Vec<Self>;
}

impl<E: Environment> ZeroExtend for Boolean<E> {
    fn zero_extend(bits: &[Boolean<E>], length: usize) -> Vec<Boolean<E>> {
        if length < bits.len() {
            E::halt("Attempted to sign extend to a smaller size.")
        }
        let bits_needed = length - bits.len();

        let mut result = Vec::with_capacity(length);
        result.extend_from_slice(bits);
        // TODO (@pranav) Check that the mode is correct.
        result.extend(iter::repeat(Boolean::new(Mode::Constant, false)).take(bits_needed));

        result
    }
}
