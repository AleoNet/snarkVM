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

use core::fmt::Debug;

/// A trait to specify the Marlin mode.
pub trait MarlinMode: Clone + Debug {
    /// Specifies whether this is for a recursive proof of at least depth-1.
    const RECURSION: bool;
}

/// TODO (howardwu): Combine all of the testnet configurations into an environment struct higher up.
/// The Marlin testnet1 mode does not assume recursive proofs of any depth.
#[derive(Clone, Debug)]
pub struct MarlinTestnet1Mode;

impl MarlinMode for MarlinTestnet1Mode {
    const RECURSION: bool = false;
}

/// The Marlin testnet2 mode does not assume recursive proofs of any depth.
#[derive(Clone, Debug)]
pub struct MarlinTestnet2Mode;

impl MarlinMode for MarlinTestnet2Mode {
    const RECURSION: bool = true;
}

/// The Marlin default mode assumes a recursive proof of at least depth-1.
#[derive(Clone, Debug)]
pub struct MarlinRecursiveMode;

impl MarlinMode for MarlinRecursiveMode {
    const RECURSION: bool = true;
}
