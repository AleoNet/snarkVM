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

use super::*;
use crate::SignExtend;

impl<E: Environment, I: IntegerType, M: private::Magnitude> Shl<Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    fn shl(self, rhs: Integer<E, M>) -> Self::Output {
        self << &rhs
    }
}

impl<E: Environment, I: IntegerType, M: private::Magnitude> Shl<Integer<E, M>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn shl(self, rhs: Integer<E, M>) -> Self::Output {
        self << &rhs
    }
}

impl<E: Environment, I: IntegerType, M: private::Magnitude> Shl<&Integer<E, M>> for Integer<E, I> {
    type Output = Self;

    fn shl(self, rhs: &Integer<E, M>) -> Self::Output {
        &self << rhs
    }
}

impl<E: Environment, I: IntegerType, M: private::Magnitude> Shl<&Integer<E, M>> for &Integer<E, I> {
    type Output = Integer<E, I>;

    fn shl(self, rhs: &Integer<E, M>) -> Self::Output {
        let mut output = self.clone();
        output <<= rhs;
        output
    }
}

impl<E: Environment, I: IntegerType, M: private::Magnitude> ShlAssign<Integer<E, M>> for Integer<E, I> {
    fn shl_assign(&mut self, rhs: Integer<E, M>) {
        *self <<= &rhs
    }
}

impl<E: Environment, I: IntegerType, M: private::Magnitude> ShlAssign<&Integer<E, M>> for Integer<E, I> {
    fn shl_assign(&mut self, rhs: &Integer<E, M>) {
        // Determine the variable mode.
        if rhs.is_constant() {
            // If the shift amount is a constant, then we can manually shift in bits and truncate the result.
            let shift_amount = rhs.eject_value();
            let mut bits_le = vec![Boolean::new(self.eject_mode(), false); shift_amount.to_usize().unwrap()];

            bits_le.append(&mut self.bits_le);
            bits_le.truncate(I::BITS);

            *self = Self { bits_le, phantom: Default::default() };
        } else {
            // If the upper bits of the magnitude are set, then the result is zero.
            // Note that M::BITS >= 8.
            let result_is_zero = rhs.bits_le[7..]
                .iter()
                .fold(Boolean::new(Mode::Constant, false), |at_least_one_is_set, bit| at_least_one_is_set.or(bit));
            let zero = Self::new(Mode::Constant, I::zero());

            // Perform the left shift operation by exponentiation and multiplication.
            // Since we know that the maximum value of rhs <= 127
            // result := self * 2^{rhs}
            let shifted_integer = if I::is_signed() {
                let shift_amount_as_i128 = I128::<E>::new(Mode::Constant, 2i128).pow_wrapped(&rhs);

                // Sign-extend self.bits_le and cast as u128.
                let bits_le = Boolean::<E>::sign_extend(&self.bits_le, 128);
                let self_as_i128 = I128 { bits_le, phantom: Default::default() };

                let mut result_as_i128 = self_as_i128.mul_wrapped(&shift_amount_as_i128);

                Self { bits_le: result_as_i128.bits_le.drain(..I::BITS).collect(), phantom: Default::default() }
            } else {
                let shift_amount_as_u128 = U128::<E>::new(Mode::Constant, 2u128).pow_wrapped(&rhs);

                // Zero extend self.bits_le and cast as u128.
                let bits_le = Boolean::<E>::sign_extend(&self.bits_le, 128);
                let self_as_u128 = U128 { bits_le, phantom: Default::default() };

                let mut result_as_u128 = self_as_u128.mul_wrapped(&shift_amount_as_u128);

                Self { bits_le: result_as_u128.bits_le.drain(..I::BITS).collect(), phantom: Default::default() }
            };

            *self = Self::ternary(&result_is_zero, &zero, &shifted_integer);
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::UniformRand;

    use rand::thread_rng;

    const ITERATIONS: usize = 128;
}
