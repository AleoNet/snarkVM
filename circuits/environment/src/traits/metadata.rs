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

use crate::{CircuitCount, Mode, StaticParameter};

/// Trait for determining the number of constants, public input, private inputs, and constraints for an operation.
pub trait Count<Op: ?Sized> {
    type Case: StaticParameter + ?Sized;

    /// Returns the number of constants, public inputs, private inputs, and constraints.
    fn count(parameter: &Self::Case) -> CircuitCount;
}

/// Trait for determining the mode of the output of an operation.
pub trait OutputMode<Op: ?Sized> {
    type Case: StaticParameter + ?Sized;

    /// Returns the mode of the output.
    fn output_mode(input: &Self::Case) -> Mode;
}
