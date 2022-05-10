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

impl<E: Environment> Adder for Boolean<E> {
    type Carry = Boolean<E>;
    type Sum = Boolean<E>;

    /// Returns the sum of `self` and `other` as a sum bit and carry bit.
    fn adder(&self, other: &Self, carry: &Self) -> (Self::Sum, Self::Carry) {
        // Compute the sum bit.
        let c0 = self ^ other;
        let sum = &c0 ^ carry;

        // Compute the carry bit.
        let c1 = self & other;
        let c2 = carry & c0;
        let carry = c1 | c2;

        (sum, carry)
    }
}

impl<E: Environment> Metadata<dyn Adder<Carry = Boolean<E>, Sum = Boolean<E>>> for Boolean<E> {
    type Case = (CircuitType<Self>, CircuitType<Self>, CircuitType<Self>);
    type OutputType = (CircuitType<Self>, CircuitType<Self>);

    fn count(case: &Self::Case) -> Count {
        let (lhs, rhs, carry) = case.clone();

        let case = (lhs, rhs);
        let c0_count = count!(Boolean<E>, BitXor<Boolean<E>, Output = Boolean<E>>, &case);
        let c1_count = count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
        let c0_output_type = output_type!(Boolean<E>, BitXor<Boolean<E>, Output = Boolean<E>>, case.clone());
        let c1_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

        let case = (c0_output_type.clone(), carry.clone());
        let sum_count = count!(Boolean<E>, BitXor<Boolean<E>, Output = Boolean<E>>, &case);

        let case = (carry, c0_output_type);
        let c2_count = count!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, &case);
        let c2_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, case);

        let carry_count = count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &(c1_output_type, c2_output_type));

        c0_count + c1_count + sum_count + c2_count + carry_count
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs, carry) = case.clone();
        let c0_output_type =
            output_type!(Boolean<E>, BitXor<Boolean<E>, Output = Boolean<E>>, (lhs.clone(), rhs.clone()));
        let c1_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, (lhs, rhs));

        let sum_output_type =
            output_type!(Boolean<E>, BitXor<Boolean<E>, Output = Boolean<E>>, (c0_output_type.clone(), carry.clone()));
        let c2_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output = Boolean<E>>, (carry, c0_output_type));

        let carry_output_type =
            output_type!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, (c1_output_type, c2_output_type));

        (sum_output_type, carry_output_type)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_adder(
        name: &str,
        expected_sum: bool,
        expected_carry: bool,
        a: Boolean<Circuit>,
        b: Boolean<Circuit>,
        c: Boolean<Circuit>,
    ) {
        Circuit::scope(name, || {
            let case = format!("({} ADD {} WITH {})", a.eject_value(), b.eject_value(), c.eject_value());
            let (candidate_sum, candidate_carry) = a.adder(&b, &c);
            assert_eq!(expected_sum, candidate_sum.eject_value(), "SUM {}", case);
            assert_eq!(expected_carry, candidate_carry.eject_value(), "CARRY {}", case);

            let case = (CircuitType::from(a), CircuitType::from(b), CircuitType::from(c));
            assert_count!(Boolean<Circuit>, Adder<Carry = Boolean<Circuit>, Sum = Boolean<Circuit>>, &case);
            let (sum_type, carry_type) =
                output_type!(Boolean<Circuit>, Adder<Carry = Boolean<Circuit>, Sum = Boolean<Circuit>>, case);

            assert_eq!(sum_type.eject_mode(), candidate_sum.eject_mode());
            if sum_type.is_constant() {
                assert_eq!(sum_type.eject_value(), candidate_sum.eject_value());
            }

            assert_eq!(carry_type.eject_mode(), candidate_carry.eject_mode());
            if carry_type.is_constant() {
                assert_eq!(carry_type.eject_value(), candidate_carry.eject_value());
            }
        });
    }

    fn run_test(mode_a: Mode, mode_b: Mode, mode_c: Mode) {
        for first in [true, false] {
            for second in [true, false] {
                for third in [true, false] {
                    let a = Boolean::new(mode_a, first);
                    let b = Boolean::new(mode_b, second);
                    let c = Boolean::new(mode_c, third);

                    let expected_sum = first ^ second ^ third;
                    let expected_carry = (first & second) | (third & (first ^ second));

                    let name = format!("({} ADD {} WITH {})", mode_a, mode_b, mode_c);
                    check_adder(&name, expected_sum, expected_carry, a, b, c);
                }
            }
        }
    }

    #[test]
    fn check_constant_add_constant_with_constant() {
        run_test(Mode::Constant, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn check_constant_add_constant_with_public() {
        run_test(Mode::Constant, Mode::Constant, Mode::Public);
    }

    #[test]
    fn check_constant_add_constant_with_private() {
        run_test(Mode::Constant, Mode::Constant, Mode::Private);
    }

    // Disabling this test due to variable modes in repeated XORing.
    // TODO: Resolve this case.
    // #[test]
    // fn check_constant_add_public_with_constant() {
    //     run_test(Mode::Constant, Mode::Public, Mode::Constant);
    // }

    #[test]
    fn check_constant_add_public_with_public() {
        run_test(Mode::Constant, Mode::Public, Mode::Public);
    }

    #[test]
    fn check_constant_add_public_with_private() {
        run_test(Mode::Constant, Mode::Public, Mode::Private);
    }

    #[test]
    fn check_constant_add_private_with_constant() {
        run_test(Mode::Constant, Mode::Private, Mode::Constant);
    }

    #[test]
    fn check_constant_add_private_with_public() {
        run_test(Mode::Constant, Mode::Private, Mode::Public);
    }

    #[test]
    fn check_constant_add_private_with_private() {
        run_test(Mode::Constant, Mode::Private, Mode::Private);
    }

    // Disabling this test due to variable modes in repeated XORing.
    // TODO: Resolve this case.
    // #[test]
    // fn check_public_add_constant_with_constant() {
    //     run_test(Mode::Public, Mode::Constant, Mode::Constant);
    // }

    #[test]
    fn check_public_add_constant_with_public() {
        run_test(Mode::Public, Mode::Constant, Mode::Public);
    }

    #[test]
    fn check_public_add_constant_with_private() {
        run_test(Mode::Public, Mode::Constant, Mode::Private);
    }

    #[test]
    fn check_public_add_public_with_constant() {
        run_test(Mode::Public, Mode::Public, Mode::Constant);
    }

    #[test]
    fn check_public_add_public_with_public() {
        run_test(Mode::Public, Mode::Public, Mode::Public);
    }

    #[test]
    fn check_public_add_public_with_private() {
        run_test(Mode::Public, Mode::Public, Mode::Private);
    }

    #[test]
    fn check_public_add_private_with_constant() {
        run_test(Mode::Public, Mode::Private, Mode::Constant);
    }

    #[test]
    fn check_public_add_private_with_public() {
        run_test(Mode::Public, Mode::Private, Mode::Public);
    }

    #[test]
    fn check_public_add_private_with_private() {
        run_test(Mode::Public, Mode::Private, Mode::Private);
    }

    #[test]
    fn check_private_add_constant_with_constant() {
        run_test(Mode::Private, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn check_private_add_constant_with_public() {
        run_test(Mode::Private, Mode::Constant, Mode::Public);
    }

    #[test]
    fn check_private_add_constant_with_private() {
        run_test(Mode::Private, Mode::Constant, Mode::Private);
    }

    #[test]
    fn check_private_add_public_with_constant() {
        run_test(Mode::Private, Mode::Public, Mode::Constant);
    }

    #[test]
    fn check_private_add_public_with_public() {
        run_test(Mode::Private, Mode::Public, Mode::Public);
    }

    #[test]
    fn check_private_add_public_with_private() {
        run_test(Mode::Private, Mode::Public, Mode::Private);
    }

    #[test]
    fn check_private_add_private_with_constant() {
        run_test(Mode::Private, Mode::Private, Mode::Constant);
    }

    #[test]
    fn check_private_add_private_with_public() {
        run_test(Mode::Private, Mode::Private, Mode::Public);
    }

    #[test]
    fn check_private_add_private_with_private() {
        run_test(Mode::Private, Mode::Private, Mode::Private);
    }
}
