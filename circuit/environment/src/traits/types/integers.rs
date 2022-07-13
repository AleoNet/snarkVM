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

use crate::prelude::*;

/// Representation of an integer.
pub trait IntegerTrait<I: IntegerType, U8: IntegerCore<u8>, U16: IntegerCore<u16>, U32: IntegerCore<u32>>:
    IntegerCore<I>
    + PowChecked<U8, Output = Self>
    + PowWrapped<U8, Output = Self>
    + Shl<U8, Output = Self>
    + ShlAssign<U8>
    + ShlChecked<U8, Output = Self>
    + ShlWrapped<U8, Output = Self>
    + Shr<U8, Output = Self>
    + ShrAssign<U8>
    + ShrChecked<U8, Output = Self>
    + ShrWrapped<U8, Output = Self>
    + PowChecked<U16, Output = Self>
    + PowWrapped<U16, Output = Self>
    + Shl<U16, Output = Self>
    + ShlAssign<U16>
    + ShlChecked<U16, Output = Self>
    + ShlWrapped<U16, Output = Self>
    + Shr<U16, Output = Self>
    + ShrAssign<U16>
    + ShrChecked<U16, Output = Self>
    + ShrWrapped<U16, Output = Self>
    + PowChecked<U32, Output = Self>
    + PowWrapped<U32, Output = Self>
    + Shl<U32, Output = Self>
    + ShlAssign<U32>
    + ShlChecked<U32, Output = Self>
    + ShlWrapped<U32, Output = Self>
    + Shr<U32, Output = Self>
    + ShrAssign<U32>
    + ShrChecked<U32, Output = Self>
    + ShrWrapped<U32, Output = Self>
{
}

pub trait IntegerCore<I: IntegerType>:
    AbsChecked
    + AbsWrapped
    + AddAssign
    + Add<Output = Self>
    + AddChecked<Output = Self>
    + AddWrapped<Output = Self>
    + BitAndAssign
    + BitAnd<Output = Self>
    + BitOrAssign
    + BitOr<Output = Self>
    + BitXorAssign
    + BitXor<Output = Self>
    + Clone
    + Compare
    + DivAssign
    + Div<Output = Self>
    + DivChecked<Output = Self>
    + DivWrapped<Output = Self>
    + Eject
    + Equal
    + FromBits
    + Inject
    + MulAssign
    + Mul<Output = Self>
    + MulChecked<Output = Self>
    + MulWrapped<Output = Self>
    + Neg<Output = Self>
    + Not<Output = Self>
    + One
    + Parser
    + SubAssign
    + Sub<Output = Self>
    + SubChecked<Output = Self>
    + SubWrapped<Output = Self>
    + Ternary
    + ToBits
    + TypeName
    + Zero
{
}
