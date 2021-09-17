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

macro_rules! dpc_setup {
    ($parameter: ident, $fn_name: ident, $type_name: ident, $setup_msg: expr) => {
        #[inline]
        fn $fn_name() -> &'static Self::$type_name {
            static PARAMETER: OnceCell<<$parameter as Parameters>::$type_name> = OnceCell::new();
            PARAMETER.get_or_init(|| Self::$type_name::setup($setup_msg))
        }
    };
}

#[rustfmt::skip]
macro_rules! dpc_snark_setup {
    ($network_parameters: ident, $fn_name: ident, $snark_type: ident, $key_type: ident, $parameter: ident, $message: expr) => {
        #[inline]
        fn $fn_name() -> &'static <Self::$snark_type as SNARK>::$key_type {
            static PARAMETER: OnceCell<<<$network_parameters as Parameters>::$snark_type as SNARK>::$key_type> = OnceCell::new();
            PARAMETER.get_or_init(|| {
                <Self::$snark_type as SNARK>::$key_type::read_le(
                    $parameter::load_bytes().expect(&format!("Failed to load parameter bytes for {}", $message)).as_slice()
                ).expect(&format!("Failed to read {} from bytes", $message))
            })
        }
    };
}

#[rustfmt::skip]
macro_rules! dpc_snark_setup_with_mode {
    ($network_parameters: ident, $fn_name: ident, $snark_type: ident, $key_type: ident, $parameter: ident, $message: expr) => {
        #[inline]
        fn $fn_name(is_prover: bool) -> &'static Option<<Self::$snark_type as SNARK>::$key_type> {
            match is_prover {
                true => {
                    static PARAMETER: OnceCell<Option<<<$network_parameters as Parameters>::$snark_type as SNARK>::$key_type>> = OnceCell::new();
                    PARAMETER.get_or_init(|| {
                        Some(<Self::$snark_type as SNARK>::$key_type::read_le(
                            $parameter::load_bytes().expect(&format!("Failed to load parameter bytes for {}", $message)).as_slice(),
                        ).expect(&format!("Failed to read {} from bytes", $message)))
                    })
                }
                false => &None,
            }
        }
    };
}
