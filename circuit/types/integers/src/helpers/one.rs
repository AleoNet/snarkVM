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

impl<E: Environment, I: IntegerType> One for Integer<E, I> {
    type Boolean = Boolean<E>;

    fn one() -> Self {
        Integer::constant(console::Integer::one())
    }

    fn is_one(&self) -> Self::Boolean {
        self.is_equal(&Integer::one())
    }
}

impl<E: Environment, I: IntegerType> Metrics<dyn One<Boolean = Boolean<E>>> for Integer<E, I> {
    type Case = ();

    fn count(_case: &Self::Case) -> Count {
        Count::is(I::BITS, 0, 0, 0)
    }
}

impl<E: Environment, I: IntegerType> OutputMode<dyn One<Boolean = Boolean<E>>> for Integer<E, I> {
    type Case = ();

    fn output_mode(_case: &Self::Case) -> Mode {
        Mode::Constant
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    fn check_one<I: IntegerType>() {
        Circuit::scope("One", || {
            assert_scope!(0, 0, 0, 0);
            let candidate = Integer::<Circuit, I>::one();
            assert_eq!(console::Integer::one(), candidate.eject_value());
            assert_count!(One<Boolean>() => Integer<I>, &());
            assert_output_mode!(One<Boolean>() => Integer<I>, &(), candidate);
        });
        // Should equal 1.
        assert!(Integer::<Circuit, I>::one().is_one().eject_value());
        // Should not equal 0.
        assert!(!Integer::<Circuit, I>::one().is_zero().eject_value());
        // Reset the circuit.
        Circuit::reset();
    }

    test_integer_static!(check_one, i8, one);
    test_integer_static!(check_one, i16, one);
    test_integer_static!(check_one, i32, one);
    test_integer_static!(check_one, i64, one);
    test_integer_static!(check_one, i128, one);

    test_integer_static!(check_one, u8, one);
    test_integer_static!(check_one, u16, one);
    test_integer_static!(check_one, u32, one);
    test_integer_static!(check_one, u64, one);
    test_integer_static!(check_one, u128, one);
}
