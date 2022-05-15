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

impl<E: Environment> ToBitsBE for Boolean<E> {
    type Boolean = Boolean<E>;

    /// Outputs `self` as a single-element vector.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        (&self).to_bits_be()
    }
}

impl<E: Environment> ToBitsBE for &Boolean<E> {
    type Boolean = Boolean<E>;

    /// Outputs `self` as a single-element vector.
    fn to_bits_be(&self) -> Vec<Self::Boolean> {
        vec![(*self).clone()]
    }
}

impl<E: Environment> Metadata<dyn ToBitsBE<Boolean = Boolean<E>>> for Boolean<E> {
    type Case = CircuitType<Self>;
    type OutputType = Vec<CircuitType<Self>>;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(constant) => {
                constant.circuit().to_bits_be().into_iter().map(CircuitType::from).collect()
            }
            CircuitType::Public => vec![CircuitType::Public],
            CircuitType::Private => vec![CircuitType::Private],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_to_bits_be(name: &str, expected: &[bool], candidate: Boolean<Circuit>) {
        Circuit::scope(name, || {
            let result = candidate.to_bits_be();
            assert_eq!(1, result.len());
            for (expected_bit, candidate_bit) in expected.iter().zip_eq(result.iter()) {
                assert_eq!(*expected_bit, candidate_bit.eject_value());
            }

            let case = CircuitType::from(candidate);
            assert_count!(ToBitsBE<Boolean>() => Boolean, &case);
            assert_output_type!(ToBitsBE<Boolean>() => Boolean, case, result);
        });
    }

    #[test]
    fn test_to_bits_be_constant() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        check_to_bits_be("Constant", &[true], candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        check_to_bits_be("Constant", &[false], candidate);
    }

    #[test]
    fn test_to_bits_be_public() {
        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        check_to_bits_be("Public", &[true], candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        check_to_bits_be("Public", &[false], candidate);
    }

    #[test]
    fn test_to_bits_be_private() {
        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        check_to_bits_be("Private", &[true], candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        check_to_bits_be("Private", &[false], candidate);
    }
}
