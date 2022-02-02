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
use crate::Zero;
use itertools::rev;

// TODO (@pranav) Documentation.
impl<E: Environment, I: IntegerType> Integer<E, I> {
    pub(crate) fn add_bits_in_field(this_bits_le: &[Boolean<E>], that_bits_le: &[Boolean<E>]) -> Vec<Boolean<E>> {
        // Instead of adding the bits of `self` and `other` directly, the integers are
        // converted into a field elements, and summed, before being converted back to integers.
        // Note: This is safe as the field is larger than the maximum integer type supported.
        let this = BaseField::from_bits_le(Mode::Private, &this_bits_le);
        let that = BaseField::from_bits_le(Mode::Private, &that_bits_le);
        let sum = this + that;

        // Extract the integer bits from the field element, with a carry bit.
        sum.to_lower_bits_le(I::BITS + 1)
    }

    pub(crate) fn divide_bits_in_field(this_bits_le: &[Boolean<E>], that_bits_le: &[Boolean<E>]) -> Vec<Boolean<E>> {
        // Instead of dividing the bits of `self` and `other` directly, the integers are
        // converted into a field elements, and divided, before being converted back to integers.
        // Note: This is safe as the field is larger than the maximum integer type supported.
        let divisor = BaseField::from_bits_le(Mode::Private, &that_bits_le);
        // Enforce that the divisor is not zero.
        E::assert_eq(divisor.is_eq(&BaseField::zero()), E::zero());

        // Unsigned maximum of size I::BITS
        let max = BaseField::from_bits_le(Mode::Constant, &vec![Boolean::new(Mode::Constant, true); I::BITS]);

        let mut quotient_bits = Vec::with_capacity(I::BITS);
        let mut remainder = BaseField::<E>::zero();

        for bit in this_bits_le.into_iter().rev() {
            remainder = remainder.double();
            remainder = remainder + BaseField::from(bit);

            // Check that remainder is greater than or equal to divisor, via an unsigned overflow check.
            //   - difference := I:MAX + (b - a).
            //   - If difference > I::MAX, then b > a.
            //   - If difference <= I::MAX, then a >= b.
            //   - Note that difference > I::MAX if carry_bit is set.
            let difference = &max + (&divisor - &remainder);
            let bits = difference.to_lower_bits_le(I::BITS + 1);
            let carry_bit = bits.last().unwrap();
            // This is safe since we extract at least one bit from the difference.
            let remainder_is_gte_divisor = carry_bit.not();

            remainder = BaseField::ternary(&remainder_is_gte_divisor, &(&remainder - &divisor), &remainder);
            quotient_bits.push(remainder_is_gte_divisor);
        }

        // Reverse and return the quotient bits.
        quotient_bits.reverse();
        quotient_bits
    }

    pub(crate) fn multiply_bits_in_field(
        this_bits_le: &[Boolean<E>],
        that_bits_le: &[Boolean<E>],
        extract_upper_bits: bool,
    ) -> Vec<Boolean<E>> {
        if 2 * I::BITS < E::BaseField::size_in_bits() - 1 {
            // Instead of multiplying the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and multiplied, before being converted back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let this = BaseField::from_bits_le(Mode::Private, this_bits_le);
            let that = BaseField::from_bits_le(Mode::Private, that_bits_le);
            let product = this * that;

            // Extract the integer bits from the field element, with the carry bits.
            product.to_lower_bits_le(2 * I::BITS)
        } else if (I::BITS + I::BITS / 2) < E::BaseField::size_in_bits() - 1 {
            // Perform multiplication by decomposing it into separate operations on its
            // upper and lower bits.
            // See this page for reference: https://en.wikipedia.org/wiki/Karatsuba_algorithm.
            // Note that we follow the naming convention given in the `Basic Step` section of
            // the above page.
            let x_1 = BaseField::from_bits_le(Mode::Private, &this_bits_le[(I::BITS / 2)..]);
            let x_0 = BaseField::from_bits_le(Mode::Private, &this_bits_le[..(I::BITS / 2)]);
            let y_1 = BaseField::from_bits_le(Mode::Private, &that_bits_le[(I::BITS / 2)..]);
            let y_0 = BaseField::from_bits_le(Mode::Private, &that_bits_le[..(I::BITS / 2)]);

            let z_0 = &x_0 * &y_0;
            let z_1 = (&x_1 * &y_0) + (&x_0 * &y_1);

            let mut b_m_bits = vec![Boolean::new(Mode::Constant, false); I::BITS / 2];
            b_m_bits.push(Boolean::new(Mode::Constant, true));

            let b_m = BaseField::from_bits_le(Mode::Constant, &b_m_bits);
            let z_0_plus_z_1 = &z_0 + (&z_1 * &b_m);

            let mut bits_le = z_0_plus_z_1.to_lower_bits_le(I::BITS + I::BITS / 2 + 1);

            // Only `mul_checked` requires these bits to perform overflow/underflow checks.
            if extract_upper_bits {
                let z_2 = &x_1 * &y_1;
                bits_le.append(&mut z_2.to_lower_bits_le(I::BITS));
            }

            bits_le
        } else {
            // TODO (@pranav) Do we need to handle this case? The current integers can
            //   be handled by the code above.
            todo!()
        }
    }

    pub(crate) fn subtract_bits_in_field(this_bits_le: &[Boolean<E>], that_bits_le: &[Boolean<E>]) -> Vec<Boolean<E>> {
        // Instead of subtracting the bits of `self` and `other` directly, the integers are
        // converted into a field elements, and subtracted, before being converted back to integers.
        // Note: This is safe as the field is larger than the maximum integer type supported.
        let this = BaseField::from_bits_le(Mode::Private, &this_bits_le);
        let that = BaseField::from_bits_le(Mode::Private, &that_bits_le.iter().map(|b| !b).collect::<Vec<_>>());
        let difference = this + &that + BaseField::one();

        // Extract the integer bits from the field element, with a carry bit.
        difference.to_lower_bits_le(I::BITS + 1)
    }
}
