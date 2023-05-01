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

pub mod error;
pub use error::*;

mod helpers;
pub use helpers::*;

mod impls;
pub use impls::*;

mod flags;
pub use flags::*;

mod traits;
pub use traits::*;

#[cfg(feature = "derive")]
pub use snarkvm_utilities_derives::*;

/// Return the number of (byte-aligned) bits and bytes required to represent the given number of bits.
///
/// Examples:
/// - Given `64 bits`, returns `(64, 8)`.
/// - Given `251 bits`, returns `(256, 32)`.
/// - Given `999 bits`, returns `(1000, 125)`.
#[inline]
pub const fn number_of_bits_and_bytes(num_bits: usize) -> (usize, usize) {
    let byte_size = number_of_bits_to_number_of_bytes(num_bits);
    ((byte_size * 8), byte_size)
}

/// Return the number of bytes required to represent the given number of bits.
#[inline]
pub const fn number_of_bits_to_number_of_bytes(num_bits: usize) -> usize {
    (num_bits + 7) / 8
}

#[test]
fn test_number_of_bits_and_bytes() {
    assert_eq!((64, 8), number_of_bits_and_bytes(64));
    assert_eq!((256, 32), number_of_bits_and_bytes(251));
    assert_eq!((1000, 125), number_of_bits_and_bytes(999));
}
