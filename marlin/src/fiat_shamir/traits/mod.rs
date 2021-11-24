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

pub use snarkvm_algorithms::traits::{AlgebraicSponge, DefaultCapacityAlgebraicSponge, DuplexSpongeMode};

pub use snarkvm_gadgets::traits::{AlgebraicSpongeVar, DefaultCapacityAlgebraicSpongeVar};

mod fiat_shamir;
pub use fiat_shamir::*;

mod fiat_shamir_gadget;
pub use fiat_shamir_gadget::*;
