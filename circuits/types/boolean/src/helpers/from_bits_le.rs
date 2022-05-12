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

impl<E: Environment> FromBitsLE for Boolean<E> {
    type Boolean = Boolean<E>;

    /// Returns a boolean circuit given a mode and single boolean.
    fn from_bits_le(bits_le: &[Self::Boolean]) -> Self {
        // Ensure there is exactly one boolean in the list of booleans.
        match bits_le.len() == 1 {
            true => bits_le[0].clone(),
            false => E::halt(format!("Attempted to instantiate a boolean with {} bits", bits_le.len())),
        }
    }
}

impl<E: Environment> Metadata<dyn FromBitsLE<Boolean = Boolean<E>>> for Boolean<E> {
    type Case = CircuitType<Vec<Self>>;
    type OutputType = CircuitType<Self>;

    fn count(_case: &Self::Case) -> Count {
        Count::is(0, 0, 0, 0)
    }

    fn output_type(case: Self::Case) -> Self::OutputType {
        match case {
            CircuitType::Constant(constant) => CircuitType::from(Boolean::from_bits_le(&constant.circuit())),
            CircuitType::Public => CircuitType::Public,
            CircuitType::Private => CircuitType::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    fn check_from_bits_le(name: &str, expected: bool, candidate: &Boolean<Circuit>) {
        Circuit::scope(name, || {
            let result = Boolean::from_bits_le(&[(*candidate).clone()]);
            assert_eq!(expected, result.eject_value());

            let case = CircuitType::from(vec![candidate.clone()]);
            assert_count!(Boolean<Circuit>, FromBitsLE<Boolean = Boolean<Circuit>>, &case);
            assert_output_type!(Boolean<Circuit>, FromBitsLE<Boolean = Boolean<Circuit>>, case, result);
        });
        Circuit::reset();
    }

    #[test]
    fn test_from_bits_constant() {
        let candidate = Boolean::<Circuit>::new(Mode::Constant, true);
        check_from_bits_le("Constant", true, &candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Constant, false);
        check_from_bits_le("Constant", false, &candidate);
    }

    #[test]
    fn test_from_bits_public() {
        let candidate = Boolean::<Circuit>::new(Mode::Public, true);
        check_from_bits_le("Public", true, &candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Public, false);
        check_from_bits_le("Public", false, &candidate);
    }

    #[test]
    fn test_from_bits_private() {
        let candidate = Boolean::<Circuit>::new(Mode::Private, true);
        check_from_bits_le("Private", true, &candidate);

        let candidate = Boolean::<Circuit>::new(Mode::Private, false);
        check_from_bits_le("Private", false, &candidate);
    }
}
