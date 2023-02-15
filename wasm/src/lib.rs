// Copyright (C) 2019-2023 Aleo Systems Inc.
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

#[cfg(feature = "circuit")]
pub use snarkvm_circuit::AleoV0;

#[cfg(feature = "console")]
pub use snarkvm_console::*;

#[cfg(feature = "curves")]
pub use snarkvm_curves::{bls12_377::*, edwards_bls12::*};

#[cfg(feature = "fields")]
pub use snarkvm_fields::*;

#[cfg(feature = "synthesizer")]
pub use snarkvm_synthesizer::*;

#[cfg(feature = "utilities")]
pub use snarkvm_utilities::*;

#[cfg(test)]
mod tests;
