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

macro_rules! dpc_setup {
    ($network: ident, $fn_name: ident, $type_name: ident, $setup_msg: expr) => {
        #[inline]
        fn $fn_name() -> &'static Self::$type_name {
            static PARAMETER: OnceCell<<$network as Network>::$type_name> = OnceCell::new();
            PARAMETER.get_or_init(|| Self::$type_name::setup($setup_msg))
        }
    };
}

#[rustfmt::skip]
macro_rules! dpc_snark_setup {
    ($network: ident, $fn_name: ident, $snark_type: ident, $key_type: ident, $parameter: ident, $message: expr) => {
        #[inline]
        fn $fn_name() -> &'static <Self::$snark_type as SNARK>::$key_type {
            static PARAMETER: OnceCell<<<$network as Network>::$snark_type as SNARK>::$key_type> = OnceCell::new();
            PARAMETER.get_or_init(|| {
                <Self::$snark_type as SNARK>::$key_type::read_le(
                    $parameter::load_bytes().expect(&format!("Failed to load parameter bytes for {}", $message)).as_slice()
                ).expect(&format!("Failed to read {} from bytes", $message))
            })
        }
    };
}

/// Converts a string of 2 characters into a `u16` for a human-readable prefix in Bech32.
#[macro_export]
macro_rules! hrp2 {
    ( $persona: expr ) => {{
        snarkvm_algorithms::const_assert!($persona.len() == 2);
        let p = $persona.as_bytes();
        u16::from_le_bytes([p[0], p[1]])
    }};
}

/// Converts a string of 4 characters into a `u32` for a human-readable prefix in Bech32.
#[macro_export]
macro_rules! hrp4 {
    ( $persona: expr ) => {{
        snarkvm_algorithms::const_assert!($persona.len() == 4);
        let p = $persona.as_bytes();
        u32::from_le_bytes([p[0], p[1], p[2], p[3]])
    }};
}
