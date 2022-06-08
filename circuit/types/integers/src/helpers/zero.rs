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

impl<E: Environment, I: IntegerType> Zero for Integer<E, I> {
    type Boolean = Boolean<E>;

    fn zero() -> Self {
        Integer::constant(console::Integer::zero())
    }

    fn is_zero(&self) -> Self::Boolean {
        self.is_equal(&Integer::zero())
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn Zero<Boolean = Boolean<E>>> for Integer<E, I> {
    type Case = ();

    fn count(_case: &Self::Case) -> Count {
        Count::is(I::BITS, 0, 0, 0)
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn Zero<Boolean = Boolean<E>>> for Integer<E, I> {
    type Case = ();

    fn output_mode(_case: &Self::Case) -> Mode {
        Mode::Constant
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_zero<I: IntegerType>() {
        Circuit::scope("Zero", || {
            assert_scope!(0, 0, 0, 0);
            let candidate = Integer::<Circuit, I>::zero();
            assert_eq!(console::Integer::zero(), candidate.eject_value());
            assert_count!(Zero<Boolean>() => Integer<I>, &());
            assert_output_mode!(Zero<Boolean>() => Integer<I>, &(), candidate);
        });
        // Should equal 0.
        assert!(Integer::<Circuit, I>::zero().is_zero().eject_value());
        // Should not equal 1.
        assert!(!Integer::<Circuit, I>::zero().is_one().eject_value());
        // Reset the circuit.
        Circuit::reset();
    }

    test_integer_static!(check_zero, i8, zero);
    test_integer_static!(check_zero, i16, zero);
    test_integer_static!(check_zero, i32, zero);
    test_integer_static!(check_zero, i64, zero);
    test_integer_static!(check_zero, i128, zero);

    test_integer_static!(check_zero, u8, zero);
    test_integer_static!(check_zero, u16, zero);
    test_integer_static!(check_zero, u32, zero);
    test_integer_static!(check_zero, u64, zero);
    test_integer_static!(check_zero, u128, zero);
}
