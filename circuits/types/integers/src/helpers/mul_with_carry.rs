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

use super::*;

/// A binary operator that returns the product of two operands and associated carry bits.
pub(crate) trait MulWithCarry {
    type Product;
    type Carry;

    /// Returns the product of `this` and `that` and the carry bits produced by the multiplication.
    fn mul_with_carry(this: &Self, that: &Self) -> (Self::Product, Self::Carry)
    where
        Self: Sized;
}

impl<E: Environment, I: IntegerType> MulWithCarry for Integer<E, I> {
    type Carry = Vec<Boolean<E>>;
    type Product = Self;

    /// Multiply the integer bits of `this` and `that` in the base field.
    #[inline]
    fn mul_with_carry(this: &Self, that: &Self) -> (Self::Product, Self::Carry) {
        // Case 1 - 2 integers fit in 1 field element (u8, u16, u32, u64, i8, i16, i32, i64).
        if 2 * I::BITS < (E::BaseField::size_in_bits() - 1) as u64 {
            // Instead of multiplying the bits of `self` and `other` directly, the integers are
            // converted into a field elements, and multiplied, before being converted back to integers.
            // Note: This is safe as the field is larger than the maximum integer type supported.
            let product = (this.to_field() * that.to_field()).to_lower_bits_le(2 * I::BITS as usize);

            // Split the integer bits into product bits and carry bits.
            let (bits_le, carry) = product.split_at(I::BITS as usize);

            // Return the product of `self` and `other`, along with the carry bits.
            (Integer::from_bits_le(bits_le), carry.to_vec())
        }
        // Case 2 - 1.5 integers fit in 1 field element (u128, i128).
        else if (I::BITS + I::BITS / 2) < (E::BaseField::size_in_bits() - 1) as u64 {
            // Perform multiplication by decomposing it into operations on its upper and lower bits.
            // See this page for reference: https://en.wikipedia.org/wiki/Karatsuba_algorithm.
            // Note: We follow the naming convention given in the `Basic Step` section of the cited page.
            let x_1 = Field::from_bits_le(&this.bits_le[(I::BITS as usize / 2)..]);
            let x_0 = Field::from_bits_le(&this.bits_le[..(I::BITS as usize / 2)]);
            let y_1 = Field::from_bits_le(&that.bits_le[(I::BITS as usize / 2)..]);
            let y_0 = Field::from_bits_le(&that.bits_le[..(I::BITS as usize / 2)]);

            let z_0 = &x_0 * &y_0;
            let z_1 = (&x_1 * &y_0) + (&x_0 * &y_1);

            let mut b_m_bits = vec![Boolean::constant(false); I::BITS as usize / 2];
            b_m_bits.push(Boolean::constant(true));

            let b_m = Field::from_bits_le(&b_m_bits);
            let z_0_plus_z_1 = &z_0 + (&z_1 * &b_m);

            let mut bits_le = z_0_plus_z_1.to_lower_bits_le(I::BITS as usize + I::BITS as usize / 2 + 1);

            let z_2 = &x_1 * &y_1;
            bits_le.append(&mut z_2.to_lower_bits_le(I::BITS as usize));

            // Split the integer bits into product bits and carry bits.
            let (bits_le, carry) = bits_le.split_at(I::BITS as usize);

            // Return the product of `self` and `other`, along with the carry bits.
            (Integer::from_bits_le(bits_le), carry.to_vec())
        } else {
            E::halt(format!("Multiplication of integers of size {} is not supported", I::BITS))
        }
    }
}

impl<E: Environment, I: IntegerType> Metadata<dyn MulWithCarry<Product = Integer<E, I>, Carry = Vec<Boolean<E>>>>
    for Integer<E, I>
{
    type Case = (IntegerCircuitType<E, I>, IntegerCircuitType<E, I>);
    type OutputType = (IntegerCircuitType<E, I>, Vec<CircuitType<Boolean<E>>>);

    fn count(case: &Self::Case) -> Count {
        let mut total_count = Count::zero();

        let (lhs, rhs) = case.clone();

        if 2 * I::BITS < (E::BaseField::size_in_bits() - 1) as u64 {
            // Determine the count and output type of `let product = (this.to_field() * that.to_field()).to_lower_bits_le(2 * I::BITS as usize);`.
            total_count = total_count + count!(Self, ToField<Field = Field<E>>, &lhs);
            let this_to_field_output_type = output_type!(Self, ToField<Field = Field<E>>, lhs);

            total_count = total_count + count!(Self, ToField<Field = Field<E>>, &rhs);
            let that_to_field_output_type = output_type!(Self, ToField<Field = Field<E>>, rhs);

            let case = (this_to_field_output_type, that_to_field_output_type);
            total_count = total_count + count!(Field<E>, Mul<Field<E>, Output = Field<E>>, &case);
            let field_mul_output_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (field_mul_output_type, 2 * I::BITS as usize);
            total_count = total_count + count!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, &case);
            let product_type = output_type!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, case);

            // Split the integer bits into product bits and carry bits.
            let (bits_le, _carry) = product_type.split_at(I::BITS as usize);

            // Determine the count of `Integer::from_bits_le(bits_le)`.
            total_count = total_count + count!(Integer<E, I>, FromBitsLE<Boolean = Boolean<E>>, &bits_le.to_vec());

            total_count
        }
        // Case 2 - 1.5 integers fit in 1 field element (u128, i128).
        else if (I::BITS + I::BITS / 2) < (E::BaseField::size_in_bits() - 1) as u64 {
            // Determine the count and output type of ` let x_1 = Field::from_bits_le(&self.bits_le[(I::BITS as usize / 2)..]);
            let case = lhs.bits_le[(I::BITS as usize / 2)..].to_vec();
            total_count = total_count + count!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, &case);
            let x_1_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the count and output type of ` let x_0 = Field::from_bits_le(&self.bits_le[..(I::BITS as usize / 2)]);
            let case = lhs.bits_le[..(I::BITS as usize / 2)].to_vec();
            total_count = total_count + count!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, &case);
            let x_0_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the count and output type of ` let y_1 = Field::from_bits_le(&other.bits_le[(I::BITS as usize / 2)..]);
            let case = rhs.bits_le[(I::BITS as usize / 2)..].to_vec();
            total_count = total_count + count!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, &case);
            let y_1_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the count and output type of `let y_0 = Field::from_bits_le(&other.bits_le[..(I::BITS as usize / 2)]);
            let case = rhs.bits_le[..(I::BITS as usize / 2)].to_vec();
            total_count = total_count + count!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, &case);
            let y_0_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the count and output type of `let z_0 = x_0 * y_0;`.
            let case = (x_0_type.clone(), y_0_type.clone());
            total_count = total_count + count!(Field<E>, Mul<Field<E>, Output = Field<E>>, &case);
            let z_0_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            // Determine the count and output type of `let z_1 = (x_1 * y_0) + (x_0 * y_1);`.
            let case = (x_1_type.clone(), y_0_type);
            total_count = total_count + count!(Field<E>, Mul<Field<E>, Output = Field<E>>, &case);
            let x_1_times_y_0_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (x_0_type, y_1_type.clone());
            total_count = total_count + count!(Field<E>, Mul<Field<E>, Output = Field<E>>, &case);
            let x_0_times_y_1_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (x_1_times_y_0_type, x_0_times_y_1_type);
            total_count = total_count + count!(Field<E>, Add<Field<E>, Output = Field<E>>, &case);
            let z_1_type = output_type!(Field<E>, Add<Field<E>, Output = Field<E>>, case);

            // Determine the count and output type of initializing `b_m_bits`. The source code is as follows:
            // `let mut b_m_bits = vec![Boolean::constant(false); I::BITS as usize / 2];`
            // `b_m_bits.push(Boolean::constant(true));`
            //total_count = total_count + (I::BITS / 2 + 1) * Count::is(1, 0 , 0, 0);
            let mut b_m_bits_type = vec![CircuitType::from(Boolean::constant(false)); I::BITS as usize / 2];
            b_m_bits_type.push(CircuitType::from(Boolean::constant(true)));

            // Determine the count and output type of `let b_m = Field::from_bits_le(&b_m_bits);`.
            total_count = total_count + count!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, &b_m_bits_type);
            let b_m_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, b_m_bits_type);

            // Determine the count and output type of `let z_0_plus_z_1 = &z_0 + (&z_1 + &b_m);`.
            let case = (z_1_type, b_m_type);
            total_count = total_count + count!(Field<E>, Mul<Field<E>, Output = Field<E>>, &case);
            let z_1_times_b_m_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (z_0_type, z_1_times_b_m_type);
            total_count = total_count + count!(Field<E>, Add<Field<E>, Output = Field<E>>, &case);
            let z_0_plus_z_1_type = output_type!(Field<E>, Add<Field<E>, Output = Field<E>>, case);

            // Determine the count and output type of `let mut bits_le = z_0_plus_z_1.to_lower_bits_le(I::BITS as usize + I::BITS as usize / 2 + 1);`.
            let case = (z_0_plus_z_1_type, I::BITS as usize + I::BITS as usize / 2 + 1);
            total_count = total_count + count!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, &case);
            let mut bits_le_type = output_type!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, case);

            // Determine the count and output type of `let z_2 = &x_1 * &y_1;`.
            let case = (x_1_type, y_1_type);
            total_count = total_count + count!(Field<E>, Mul<Field<E>, Output = Field<E>>, &case);
            let z_2_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            // Determine the count and output type of `bits_le.append(&mut z_2.to_lower_bits_le(I::BITS as usize));`
            let case = (z_2_type, I::BITS as usize);
            total_count = total_count + count!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, &case);
            let mut z_2_bits_le_type = output_type!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, case);
            bits_le_type.append(&mut z_2_bits_le_type);

            // Split the integer bits into product bits and carry bits.
            let (bits_le, _carry) = bits_le_type.split_at(I::BITS as usize);

            // Determine the cost of `Integer::from_bits_le(bits_le)`.
            total_count = total_count + count!(Integer<E, I>, FromBitsLE<Boolean = Boolean<E>>, &bits_le.to_vec());

            total_count
        } else {
            E::halt(format!("Multiplication of integers of size {} is not supported", I::BITS))
        }
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs) = case.clone();

        if 2 * I::BITS < (E::BaseField::size_in_bits() - 1) as u64 {
            // Determine the output type of `let product = (this.to_field() * that.to_field()).to_lower_bits_le(2 * I::BITS as usize);`.
            let this_to_field_output_type = output_type!(Self, ToField<Field = Field<E>>, lhs);

            let that_to_field_output_type = output_type!(Self, ToField<Field = Field<E>>, rhs);

            let case = (this_to_field_output_type, that_to_field_output_type);
            let field_mul_output_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (field_mul_output_type, 2 * I::BITS as usize);
            let product_type = output_type!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, case);

            // Split the integer bits into product bits and carry bits.
            let (bits_le, carry) = product_type.split_at(I::BITS as usize);

            // Determine the output type of `Integer::from_bits_le(bits_le)`.
            let integer_type = output_type!(Integer<E, I>, FromBitsLE<Boolean = Boolean<E>>, bits_le.to_vec());

            // Return the product of `self` and `other`, along with the carry bits.
            (integer_type, carry.to_vec())
        }
        // Case 2 - 1.5 integers fit in 1 field element (u128, i128).
        else if (I::BITS + I::BITS / 2) < (E::BaseField::size_in_bits() - 1) as u64 {
            // Determine the output type of ` let x_1 = Field::from_bits_le(&self.bits_le[(I::BITS as usize / 2)..]);
            let case = lhs.bits_le[(I::BITS as usize / 2)..].to_vec();
            let x_1_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the output type of ` let x_0 = Field::from_bits_le(&self.bits_le[..(I::BITS as usize / 2)]);
            let case = lhs.bits_le[..(I::BITS as usize / 2)].to_vec();
            let x_0_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the output type of ` let y_1 = Field::from_bits_le(&other.bits_le[(I::BITS as usize / 2)..]);
            let case = rhs.bits_le[(I::BITS as usize / 2)..].to_vec();
            let y_1_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the output type of `let y_0 = Field::from_bits_le(&other.bits_le[..(I::BITS as usize / 2)]);
            let case = rhs.bits_le[..(I::BITS as usize / 2)].to_vec();
            let y_0_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, case);

            // Determine the output type of `let z_0 = x_0 * y_0;`.
            let case = (x_0_type.clone(), y_0_type.clone());
            let z_0_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            // Determine the output type of `let z_1 = (x_1 * y_0) + (x_0 * y_1);`.
            let case = (x_1_type.clone(), y_0_type);
            let x_1_times_y_0_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (x_0_type, y_1_type.clone());
            let x_0_times_y_1_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (x_1_times_y_0_type, x_0_times_y_1_type);
            let z_1_type = output_type!(Field<E>, Add<Field<E>, Output = Field<E>>, case);

            // Determine the output type of initializing `b_m_bits`. The source code is as follows:
            // `let mut b_m_bits = vec![Boolean::constant(false); I::BITS as usize / 2];`
            // `b_m_bits.push(Boolean::constant(true));`
            //total_count = total_count + (I::BITS / 2 + 1) * Count::is(1, 0 , 0, 0);
            let mut b_m_bits_type = vec![CircuitType::from(Boolean::constant(false)); I::BITS as usize / 2];
            b_m_bits_type.push(CircuitType::from(Boolean::constant(true)));

            // Determine the output type of `let b_m = Field::from_bits_le(&b_m_bits);`.
            let b_m_type = output_type!(Field<E>, FromBitsLE<Boolean = Boolean<E>>, b_m_bits_type);

            // Determine the output type of `let z_0_plus_z_1 = &z_0 + (&z_1 + &b_m);`.
            let case = (z_1_type, b_m_type);
            let z_1_times_b_m_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            let case = (z_0_type, z_1_times_b_m_type);
            let z_0_plus_z_1_type = output_type!(Field<E>, Add<Field<E>, Output = Field<E>>, case);

            // Determine the output type of `let mut bits_le = z_0_plus_z_1.to_lower_bits_le(I::BITS as usize + I::BITS as usize / 2 + 1);`.
            let case = (z_0_plus_z_1_type, I::BITS as usize + I::BITS as usize / 2 + 1);
            let mut bits_le_type = output_type!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, case);

            // Determine the output type of `let z_2 = &x_1 * &y_1;`.
            let case = (x_1_type, y_1_type);
            let z_2_type = output_type!(Field<E>, Mul<Field<E>, Output = Field<E>>, case);

            // Determine the output type of `bits_le.append(&mut z_2.to_lower_bits_le(I::BITS as usize));`
            let case = (z_2_type, I::BITS as usize);
            let mut z_2_bits_le_type = output_type!(Field<E>, ToLowerBitsLE<Boolean = Boolean<E>>, case);
            bits_le_type.append(&mut z_2_bits_le_type);

            // Split the integer bits into product bits and carry bits.
            let (bits_le, carry) = bits_le_type.split_at(I::BITS as usize);

            // Determine the output type of `Integer::from_bits_le(bits_le)`.
            let integer_type = output_type!(Integer<E, I>, FromBitsLE<Boolean = Boolean<E>>, bits_le.to_vec());

            // Return the product of `self` and `other`, along with the carry bits.
            (integer_type, carry.to_vec())
        } else {
            E::halt(format!("Multiplication of integers of size {} is not supported", I::BITS))
        }
    }
}
