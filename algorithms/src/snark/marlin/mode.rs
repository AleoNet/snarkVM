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

use core::fmt::Debug;

/// A trait to specify the Marlin mode.
pub trait MarlinMode: 'static + Copy + Clone + Debug + PartialEq + Eq + Sync + Send {
    const ZK: bool;
}

/// The Marlin hiding mode produces a hiding Marlin proof.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MarlinHidingMode;

impl MarlinMode for MarlinHidingMode {
    const ZK: bool = true;
}

/// The Marlin non-hiding mode produces a non-hiding Marlin proof.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct MarlinNonHidingMode;

impl MarlinMode for MarlinNonHidingMode {
    const ZK: bool = false;
}
