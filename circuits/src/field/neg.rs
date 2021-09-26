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

impl<E: Environment> Neg for Field<E> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl<E: Environment> Neg for &Field<E> {
    type Output = Field<E>;

    fn neg(self) -> Self::Output {
        Field::<E>(-&(self.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CircuitBuilder;

    #[test]
    fn test_zero() {
        let zero = <CircuitBuilder as Environment>::Field::zero();

        let candidate = Field::<CircuitBuilder>::zero();
        assert_eq!(zero, candidate.to_value());
        assert_eq!(zero, (-&candidate).to_value());
        assert_eq!(zero, (-(-candidate)).to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, zero);
        assert_eq!(zero, candidate.to_value());
        assert_eq!(zero, (-&candidate).to_value());
        assert_eq!(zero, (-(-candidate)).to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, zero);
        assert_eq!(zero, candidate.to_value());
        assert_eq!(zero, (-&candidate).to_value());
        assert_eq!(zero, (-(-candidate)).to_value());
    }

    #[test]
    fn test_one() {
        let one = <CircuitBuilder as Environment>::Field::one();

        let candidate = Field::<CircuitBuilder>::one();
        assert_eq!(one, candidate.to_value());
        assert_eq!(-one, (-&candidate).to_value());
        assert_eq!(one, (-(-candidate)).to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Public, one);
        assert_eq!(one, candidate.to_value());
        assert_eq!(-one, (-&candidate).to_value());
        assert_eq!(one, (-(-candidate)).to_value());

        let candidate = Field::<CircuitBuilder>::new(Mode::Private, one);
        assert_eq!(one, candidate.to_value());
        assert_eq!(-one, (-&candidate).to_value());
        assert_eq!(one, (-(-candidate)).to_value());
    }
}
