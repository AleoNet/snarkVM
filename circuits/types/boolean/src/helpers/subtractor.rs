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

impl<E: Environment> Subtractor for Boolean<E> {
    type Borrow = Boolean<E>;
    type Difference = Boolean<E>;

    /// Returns the difference of `self` and `other` as a difference bit and borrow bit.
    fn subtractor(&self, other: &Self, borrow: &Self) -> (Self::Difference, Self::Borrow) {
        // Compute the difference bit.
        let c0 = self ^ other;
        println!("c0_mode: {:?}", c0.eject_mode());
        let difference = &c0 ^ borrow;
        println!("difference_mode: {:?}", difference.eject_mode());

        // Compute the borrow bit.
        let c1 = !self & other;
        println!("c1_mode: {:?}", c1.eject_mode());
        let c2 = borrow & !c0;
        println!("c2_mode: {:?}", c2.eject_mode());
        let borrow = c1 | c2;
        println!("borrow_mode: {:?}\n", borrow.eject_mode());

        (difference, borrow)
    }
}

impl<E: Environment> Metadata<dyn Subtractor<Borrow = Boolean<E>, Difference = Boolean<E>>> for Boolean<E> {
    type Case = (CircuitType<Self>, CircuitType<Self>, CircuitType<Self>);
    type OutputType = (CircuitType<Boolean<E>>, CircuitType<Boolean<E>>);

    fn count(case: &Self::Case) -> Count {
        let (lhs, rhs, borrow) = case.clone();

        let case = (lhs.clone(), rhs.clone());
        let c0_count = count!(Boolean<E>, BitXor<Boolean<E>, Output=Boolean<E>>, &case);
        let c0_output_type = output_type!(Boolean<E>, BitXor<Boolean<E>, Output=Boolean<E>>, case.clone());

        let case = (c0_output_type.clone(), borrow.clone());
        let difference_count = count!(Boolean<E>, BitXor<Boolean<E>, Output=Boolean<E>>, &case);

        let not_self_count = count!(Boolean<E>, Not<Output=Boolean<E>>, &lhs);
        let not_self_output_type = output_type!(Boolean<E>, Not<Output=Boolean<E>>, lhs);

        let case = (not_self_output_type, rhs);
        let c1_count = count!(Boolean<E>, BitAnd<Boolean<E>, Output=Boolean<E>>, &case);
        let c1_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output=Boolean<E>>, case);

        let not_c0_count = count!(Boolean<E>, Not<Output=Boolean<E>>, &c0_output_type);
        let not_c0_output_type = output_type!(Boolean<E>, Not<Output=Boolean<E>>, c0_output_type);

        let case = (borrow, not_c0_output_type);
        let c2_count = count!(Boolean<E>, BitAnd<Boolean<E>, Output=Boolean<E>>, &case);
        let c2_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output=Boolean<E>>, case);

        let borrow_count = count!(Boolean<E>, BitOr<Boolean<E>, Output = Boolean<E>>, &(c1_output_type, c2_output_type));

        c0_count + difference_count + not_self_count + c1_count + not_c0_count + c2_count + borrow_count
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        let (lhs, rhs, borrow) = case.clone();

        let c0_output_type = output_type!(Boolean<E>, BitXor<Boolean<E>, Output=Boolean<E>>, (lhs.clone(), rhs.clone()));
        println!("lhs: {:?}, rhs: {:?}", lhs, rhs);
        println!("c0_output_type: {:?}", c0_output_type);
        let difference_output_type = output_type!(Boolean<E>, BitXor<Boolean<E>, Output=Boolean<E>>, (c0_output_type.clone(), borrow.clone()));
        println!("difference_output_type: {:?}", difference_output_type);

        let not_self_output_type = output_type!(Boolean<E>, Not<Output=Boolean<E>>, lhs);
        println!("not_self_output_type: {:?}", not_self_output_type);
        let c1_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output=Boolean<E>>, (not_self_output_type, rhs));
        println!("c1_output_type: {:?}", c1_output_type);

        let not_c0_output_type = output_type!(Boolean<E>, Not<Output=Boolean<E>>, c0_output_type);
        println!("not_c0_output_type: {:?}", not_c0_output_type);
        let c2_output_type = output_type!(Boolean<E>, BitAnd<Boolean<E>, Output=Boolean<E>>, (borrow, not_c0_output_type));
        println!("c2_output_type: {:?}", c2_output_type);

        let borrow_output_type = output_type!(Boolean<E>, BitOr<Boolean<E>, Output=Boolean<E>>, (c1_output_type, c2_output_type));
        println!("borrow_output_type: {:?}", borrow_output_type);

        (difference_output_type, borrow_output_type)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_subtractor(
        name: &str,
        expected_difference: bool,
        expected_borrow: bool,
        a: Boolean<Circuit>,
        b: Boolean<Circuit>,
        c: Boolean<Circuit>,
    ) {
        Circuit::scope(name, || {
            let case = format!("({} SUB {} WITH {})", a.eject_value(), b.eject_value(), c.eject_value());
            println!("{}", case);
            let (candidate_difference, candidate_borrow) = a.subtractor(&b, &c);
            assert_eq!(expected_difference, candidate_difference.eject_value(), "DIFFERENCE {}", case);
            assert_eq!(expected_borrow, candidate_borrow.eject_value(), "BORROW {}", case);

            let case = (CircuitType::from(a), CircuitType::from(b), CircuitType::from(c));
            assert_count!(Boolean<Circuit>, Subtractor<Borrow = Boolean<Circuit>, Difference = Boolean<Circuit>>, &case);
            let (difference_type, borrow_type) = output_type!(Boolean<Circuit>, Subtractor<Borrow= Boolean<Circuit>, Difference = Boolean<Circuit>>, case);

            assert_eq!(difference_type.eject_mode(), candidate_difference.eject_mode());
            if difference_type.is_constant() {
                assert_eq!(difference_type.eject_value(), candidate_difference.eject_value());
            }

            assert_eq!(borrow_type.eject_mode(), candidate_borrow.eject_mode());
            if borrow_type.is_constant() {
                assert_eq!(borrow_type.eject_value(), candidate_borrow.eject_value());
            }
        });
    }

    fn run_test(
        mode_a: Mode,
        mode_b: Mode,
        mode_c: Mode,
    ) {
        for first in [true, false] {
            for second in [true, false] {
                for third in [true, false] {
                    let a = Boolean::new(mode_a, first);
                    let b = Boolean::new(mode_b, second);
                    let c = Boolean::new(mode_c, third);

                    let c0 = first ^ second;
                    let expected_difference = c0 ^ third;

                    let c1 = !first & second;
                    let c2 = third & !c0;
                    let expected_borrow = c1 | c2;

                    let name = format!("({} SUB {} WITH {})", mode_a, mode_b, mode_c);
                    check_subtractor(&name, expected_difference, expected_borrow, a, b, c);
                }
            }
        }
    }

    #[test]
    fn check_constant_sub_constant_with_constant() {
        run_test(Mode::Constant, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn check_constant_sub_constant_with_public() {
        run_test(Mode::Constant, Mode::Constant, Mode::Public);
    }

    #[test]
    fn check_constant_sub_constant_with_private() {
        run_test(Mode::Constant, Mode::Constant, Mode::Private);
    }

    #[test]
    fn check_constant_sub_public_with_constant() {
        run_test(Mode::Constant, Mode::Public, Mode::Constant);
    }

    #[test]
    fn check_constant_sub_public_with_public() {
        run_test(Mode::Constant, Mode::Public, Mode::Public);
    }

    #[test]
    fn check_constant_sub_public_with_private() {
        run_test(Mode::Constant, Mode::Public, Mode::Private);
    }

    #[test]
    fn check_constant_sub_private_with_constant() {
        run_test(Mode::Constant, Mode::Private, Mode::Constant);
    }

    #[test]
    fn check_constant_sub_private_with_public() {
        run_test(Mode::Constant, Mode::Private, Mode::Public);
    }

    #[test]
    fn check_constant_sub_private_with_private() {
        run_test(Mode::Constant, Mode::Private, Mode::Private);
    }

    #[test]
    fn check_public_sub_constant_with_constant() {
        run_test(Mode::Public, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn check_public_sub_constant_with_public() {
        run_test(Mode::Public, Mode::Constant, Mode::Public);
    }

    #[test]
    fn check_public_sub_constant_with_private() {
        run_test(Mode::Public, Mode::Constant, Mode::Private);
    }

    #[test]
    fn check_public_sub_public_with_constant() {
        run_test(Mode::Public, Mode::Public, Mode::Constant);
    }

    #[test]
    fn check_public_sub_public_with_public() {
        run_test(Mode::Public, Mode::Public, Mode::Public);
    }

    #[test]
    fn check_public_sub_public_with_private() {
        run_test(Mode::Public, Mode::Public, Mode::Private);
    }

    #[test]
    fn check_public_sub_private_with_constant() {
        run_test(Mode::Public, Mode::Private, Mode::Constant);
    }

    #[test]
    fn check_public_sub_private_with_public() {
        run_test(Mode::Public, Mode::Private, Mode::Public);
    }

    #[test]
    fn check_public_sub_private_with_private() {
        run_test(Mode::Public, Mode::Private, Mode::Private);
    }

    #[test]
    fn check_private_sub_constant_with_constant() {
        run_test(Mode::Private, Mode::Constant, Mode::Constant);
    }

    #[test]
    fn check_private_sub_constant_with_public() {
        run_test(Mode::Private, Mode::Constant, Mode::Public);
    }

    #[test]
    fn check_private_sub_constant_with_private() {
        run_test(Mode::Private, Mode::Constant, Mode::Private);
    }

    #[test]
    fn check_private_sub_public_with_constant() {
        run_test(Mode::Private, Mode::Public, Mode::Constant);
    }

    #[test]
    fn check_private_sub_public_with_public() {
        run_test(Mode::Private, Mode::Public, Mode::Public);
    }

    #[test]
    fn check_private_sub_public_with_private() {
        run_test(Mode::Private, Mode::Public, Mode::Private);
    }

    #[test]
    fn check_private_sub_private_with_constant() {
        run_test(Mode::Private, Mode::Private, Mode::Constant);
    }

    #[test]
    fn check_private_sub_private_with_public() {
        run_test(Mode::Private, Mode::Private, Mode::Public);
    }

    #[test]
    fn check_private_sub_private_with_private() {
        run_test(Mode::Private, Mode::Private, Mode::Private);
    }
}

