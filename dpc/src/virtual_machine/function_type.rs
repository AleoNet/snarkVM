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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FunctionType {
    Noop,
    Add,
    Update,
    Remove,
    DoubleAdd,
    DoubleRemove,
    Join,
    Split,
    Full,
}

impl FunctionType {
    pub fn input_count(&self) -> u8 {
        match self {
            Self::Noop => 0,
            Self::Add => 0,
            Self::Update => 1,
            Self::Remove => 1,
            Self::DoubleAdd => 0,
            Self::DoubleRemove => 2,
            Self::Join => 2,
            Self::Split => 1,
            Self::Full => 2,
        }
    }

    pub fn output_count(&self) -> u8 {
        match self {
            Self::Noop => 0,
            Self::Add => 1,
            Self::Update => 1,
            Self::Remove => 0,
            Self::DoubleAdd => 2,
            Self::DoubleRemove => 2,
            Self::Join => 1,
            Self::Split => 2,
            Self::Full => 2,
        }
    }
}
