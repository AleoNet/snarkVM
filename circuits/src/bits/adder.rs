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

use crate::{And, Boolean, Environment, Or, Xor};

// TODO (@pranav) Reorganize where this code is kept
//  Keeping here while prototyping

/// Single bit binary adder with carry bit
/// https://en.wikipedia.org/wiki/Adder_(electronics)#Full_adder
/// sum = (a XOR b) XOR carry
/// carry = a AND b OR carry AND (a XOR b)
/// Returns (sum, carry)
pub trait FullAdder {
    //type Boolean: BooleanTrait;
    type Output;

    fn add(&self, other: &Self, carry: &Self) -> Self::Output;
}

impl<E: Environment> FullAdder for Boolean<E> {
    //type Boolean = Boolean<E>;
    type Output = (Boolean<E>, Boolean<E>);

    fn add(&self, other: &Self, carry: &Self) -> Self::Output {
        let sum = (self.xor(other)).xor(carry);

        let c1 = self.and(other);
        let c2 = carry.and(&self.xor(other));
        let carry = c1.or(&c2);

        (sum, carry)
    }
}
