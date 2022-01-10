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

use num_traits::CheckedDiv;

impl<E: Environment, I, const SIZE: usize> Div<Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedDiv,
    bool: AsPrimitive<I>,
{
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self / &other
    }
}

impl<E: Environment, I, const SIZE: usize> Div<&Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedDiv,
    bool: AsPrimitive<I>,
{
    type Output = Self;

    fn div(self, other: &Self) -> Self::Output {
        //self * other
        todo!()
    }
}

impl<E: Environment, I, const SIZE: usize> Div<Signed<E, I, SIZE>> for &Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedDiv,
    bool: AsPrimitive<I>,
{
    type Output = Signed<E, I, SIZE>;

    fn div(self, other: Signed<E, I, SIZE>) -> Self::Output {
        (*self).clone() / other
    }
}

impl<E: Environment, I, const SIZE: usize> Div<&Signed<E, I, SIZE>> for &Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedDiv,
    bool: AsPrimitive<I>,
{
    type Output = Signed<E, I, SIZE>;

    fn div(self, other: &Signed<E, I, SIZE>) -> Self::Output {
        (*self).clone() / other
    }
}

impl<E: Environment, I, const SIZE: usize> DivAssign<Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedDiv,
    bool: AsPrimitive<I>,
{
    fn div_assign(&mut self, other: Self) {
        *self /= &other;
    }
}

impl<E: Environment, I, const SIZE: usize> DivAssign<&Self> for Signed<E, I, SIZE>
where
    I: 'static + PrimInt + NumSigned + Bounded + NumZero + NumOne + CheckedDiv,
    bool: AsPrimitive<I>,
{
    fn div_assign(&mut self, other: &Self) {
        *self = self.clone() / other;
    }
}
