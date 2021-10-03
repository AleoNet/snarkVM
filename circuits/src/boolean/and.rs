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

impl<E: Environment> And<Self> for Boolean<E> {
    type Boolean = Boolean<E>;
    type Output = Boolean<E>;

    fn and(&self, other: &Self) -> Self::Output {
        // Constant && Constant
        if self.0.is_constant() && other.0.is_constant() {
            Boolean::<E>::new(Mode::Constant, self.to_value() && other.to_value())
        }
        // Constant && Variable
        else if self.0.is_constant() {
            match self.to_value() {
                true => other.clone(),
                false => !other,
            }
        }
        // Variable && Constant
        else if other.0.is_constant() {
            match other.to_value() {
                true => self.clone(),
                false => !self,
            }
        }
        // Variable && Variable
        else {
            let output = Boolean::<E>::new(Mode::Private, self.to_value() && other.to_value());

            // Ensure `self` * `other` = `output`
            // `output` is `1` iff `self` AND `other` are both `1`.
            E::enforce(|| (self, other, &output));

            Self(output.into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Circuit;
}
