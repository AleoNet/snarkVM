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

/// Representation of a group element.
pub trait GroupTrait<S: ScalarTrait>:
    Add<Output = Self>
    + AddAssign
    + Clone
    + Double<Output = Self>
    + Eject
    + Equal
    + Inject
    + Mul<S, Output = Self>
    + MulAssign<S>
    + Neg<Output = Self>
    + Parser
    + Sub<Output = Self>
    + SubAssign
    + Ternary
    + TypeName
    + Zero
{
}
