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
use snarkvm_circuits_environment::CircuitOrMode;

impl<E: Environment> Neg for Field<E> {
    type Output = Self;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        (&self).neg()
    }
}

impl<E: Environment> Neg for &Field<E> {
    type Output = Field<E>;

    /// Performs the unary `-` operation.
    fn neg(self) -> Self::Output {
        (-&self.linear_combination).into()
    }
}

impl<E: Environment> Count<dyn Neg<Output = Field<E>>> for Field<E> {
    type Case = CircuitOrMode<Field<E>>;

    fn count(_input: &Self::Case) -> CircuitCount {
        CircuitCount::exact(0, 0, 0, 0)
    }
}

impl<E: Environment> OutputMode<dyn Neg<Output = Field<E>>> for Field<E> {
    type Case = CircuitOrMode<Field<E>>;

    fn output_mode(input: &Self::Case) -> Mode {
        match input.mode() {
            Mode::Constant => Mode::Constant,
            _ => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuits_environment::Circuit;

    // TODO: Add tests checking the count and output mode.

    #[test]
    fn test_zero() {
        let zero = <Circuit as Environment>::BaseField::zero();

        let candidate = Field::<Circuit>::zero();
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Public, zero);
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Private, zero);
        assert_eq!(zero, candidate.eject_value());
        assert_eq!(zero, (-&candidate).eject_value());
        assert_eq!(zero, (-(-candidate)).eject_value());
    }

    #[test]
    fn test_one() {
        let one = <Circuit as Environment>::BaseField::one();

        let candidate = Field::<Circuit>::one();
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Public, one);
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());

        let candidate = Field::<Circuit>::new(Mode::Private, one);
        assert_eq!(one, candidate.eject_value());
        assert_eq!(-one, (-&candidate).eject_value());
        assert_eq!(one, (-(-candidate)).eject_value());
    }
}
