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

// TODO (raychu86): Rename this circuit.
pub mod value_check_circuit;
pub use value_check_circuit::*;

pub(crate) mod value_check_private_variables;
pub(crate) use value_check_private_variables::*;

pub(crate) mod value_check_public_variables;
pub(crate) use value_check_public_variables::*;
