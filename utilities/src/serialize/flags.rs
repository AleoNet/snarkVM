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

use crate::serialize::Flags;

/// Flags to be encoded into the serialization.
#[derive(Default, Clone, Copy, PartialEq, Eq)]
pub struct EmptyFlags;

impl Flags for EmptyFlags {
    const BIT_SIZE: usize = 0;

    #[inline]
    fn u8_bitmask(&self) -> u8 {
        0
    }

    #[inline]
    fn from_u8(value: u8) -> Option<Self> {
        if (value >> 7) == 0 { Some(EmptyFlags) } else { None }
    }
}

/// Flags to be encoded into the serialization.
/// The default flags (empty) should not change the binary representation.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SWFlags {
    Infinity,
    PositiveY,
    NegativeY,
}

impl SWFlags {
    #[inline]
    pub fn infinity() -> Self {
        SWFlags::Infinity
    }

    #[inline]
    pub fn from_y_sign(is_positive: bool) -> Self {
        if is_positive { SWFlags::PositiveY } else { SWFlags::NegativeY }
    }

    #[inline]
    pub fn is_infinity(&self) -> bool {
        matches!(self, SWFlags::Infinity)
    }

    #[inline]
    pub fn is_positive(&self) -> Option<bool> {
        match self {
            SWFlags::Infinity => None,
            SWFlags::PositiveY => Some(true),
            SWFlags::NegativeY => Some(false),
        }
    }
}

impl Default for SWFlags {
    #[inline]
    fn default() -> Self {
        // NegativeY doesn't change the serialization
        SWFlags::NegativeY
    }
}

impl Flags for SWFlags {
    const BIT_SIZE: usize = 2;

    #[inline]
    fn u8_bitmask(&self) -> u8 {
        let mut mask = 0;
        match self {
            SWFlags::Infinity => mask |= 1 << 6,
            SWFlags::PositiveY => mask |= 1 << 7,
            _ => (),
        }
        mask
    }

    #[inline]
    fn from_u8(value: u8) -> Option<Self> {
        let x_sign = (value >> 7) & 1 == 1;
        let is_infinity = (value >> 6) & 1 == 1;
        match (x_sign, is_infinity) {
            // This is invalid because we only want *one* way to serialize
            // the point at infinity.
            (true, true) => None,
            (false, true) => Some(SWFlags::Infinity),
            (true, false) => Some(SWFlags::PositiveY),
            (false, false) => Some(SWFlags::NegativeY),
        }
    }
}

/// Flags to be encoded into the serialization.
/// The default flags (empty) should not change the binary representation.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum EdwardsFlags {
    PositiveY,
    NegativeY,
}

impl EdwardsFlags {
    #[inline]
    pub fn from_y_sign(is_positive: bool) -> Self {
        if is_positive { EdwardsFlags::PositiveY } else { EdwardsFlags::NegativeY }
    }

    #[inline]
    pub fn is_positive(&self) -> bool {
        match self {
            EdwardsFlags::PositiveY => true,
            EdwardsFlags::NegativeY => false,
        }
    }
}

impl Default for EdwardsFlags {
    #[inline]
    fn default() -> Self {
        // NegativeY doesn't change the serialization
        EdwardsFlags::NegativeY
    }
}

impl Flags for EdwardsFlags {
    const BIT_SIZE: usize = 1;

    #[inline]
    fn u8_bitmask(&self) -> u8 {
        let mut mask = 0;
        if let Self::PositiveY = self {
            mask |= 1 << 7;
        }
        mask
    }

    #[inline]
    fn from_u8(value: u8) -> Option<Self> {
        let x_sign = (value >> 7) & 1 == 1;
        if x_sign { Some(Self::PositiveY) } else { Some(Self::NegativeY) }
    }
}
