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

/// A trait to specify the Marlin mode.
pub trait MarlinMode: Clone {
    /// Specifies whether this is for a recursive proof of at least depth-1.
    const RECURSION: bool;
}

/// The Marlin default mode does not assume recursive proofs of any depth.
#[derive(Clone)]
pub struct MarlinDefaultMode;

impl MarlinMode for MarlinDefaultMode {
    const RECURSION: bool = false;
}

/// The Marlin default mode assumes a recursive proof of at least depth-1.
#[derive(Clone)]
pub struct MarlinRecursiveMode;

impl MarlinMode for MarlinRecursiveMode {
    const RECURSION: bool = true;
}
