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

#[macro_export]
macro_rules! checksum {
    ($bytes: expr) => {
        hex::encode(snarkvm_algorithms::crh::sha256::sha256($bytes))
    };
}

#[macro_export]
macro_rules! checksum_error {
    ($expected: expr, $candidate: expr) => {
        Err(crate::errors::ParameterError::ChecksumMismatch($expected, $candidate))
    };
}

#[macro_export]
macro_rules! impl_params_local {
    ($name: ident, $test_name: ident, $local_dir: expr, $fname: tt, $size: tt) => {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct $name;

        impl crate::traits::Parameter for $name {
            const CHECKSUM: &'static str = include_str!(concat!($local_dir, $fname, ".checksum"));
            const SIZE: u64 = $size;

            fn load_bytes() -> Result<Vec<u8>, crate::errors::ParameterError> {
                let buffer = include_bytes!(concat!($local_dir, $fname, ".params"));
                let checksum = checksum!(buffer);

                match Self::CHECKSUM == checksum {
                    true => Ok(buffer.to_vec()),
                    false => checksum_error!(Self::CHECKSUM.into(), checksum),
                }
            }
        }

        #[cfg(test)]
        #[test]
        fn $test_name() {
            use crate::traits::Parameter;

            let parameters = $name::load_bytes().expect("failed to load parameters");
            assert_eq!($name::SIZE, parameters.len() as u64);
        }
    };
}

#[macro_export]
macro_rules! impl_params_remote {
    ($name: ident, $test_name: ident, $remote_url: tt, $local_dir: expr, $filename: tt, $size: tt) => {
        pub struct $name;

        impl crate::traits::Parameter for $name {
            const CHECKSUM: &'static str = include_str!(concat!($local_dir, $filename, ".checksum"));
            const SIZE: u64 = $size;

            fn load_bytes() -> Result<Vec<u8>, crate::errors::ParameterError> {
                let parameters = crate::check_parameters::CheckParameters::new($filename, $remote_url, Self::CHECKSUM);
                parameters.load_bytes()
            }
        }

        #[cfg(test)]
        #[test]
        fn $test_name() {
            use crate::traits::Parameter;

            let parameters = $name::load_bytes().expect("failed to load parameters");
            assert_eq!($name::SIZE, parameters.len() as u64);
        }
    }
}

