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
macro_rules! impl_local {
    ($name: ident, $local_dir: expr, $fname: tt, $ftype: tt) => {
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct $name;

        impl $name {
            pub fn load_bytes() -> Result<Vec<u8>, crate::errors::ParameterError> {
                const METADATA: &'static str = include_str!(concat!($local_dir, $fname, ".metadata"));

                let metadata: serde_json::Value =
                    serde_json::from_str(METADATA).expect("Metadata was not well-formatted");
                let expected_checksum: String = metadata[concat!($ftype, "_checksum")]
                    .as_str()
                    .expect("Failed to parse checksum")
                    .to_string();
                let expected_size: usize = metadata[concat!($ftype, "_size")]
                    .to_string()
                    .parse()
                    .expect("Failed to retrieve the file size");

                let buffer = include_bytes!(concat!($local_dir, $fname, ".", $ftype));

                // Ensure the size matches.
                if expected_size != buffer.len() {
                    return Err(crate::errors::ParameterError::SizeMismatch(
                        expected_size,
                        buffer.len(),
                    ));
                }

                // Ensure the checksum matches.
                let candidate_checksum = checksum!(buffer);
                if expected_checksum != candidate_checksum {
                    return checksum_error!(expected_checksum, candidate_checksum);
                }

                return Ok(buffer.to_vec());
            }
        }

        paste::item! {
            #[cfg(test)]
            #[test]
            fn [< test_ $fname _ $ftype >]() {
                assert!($name::load_bytes().is_ok());
            }
        }
    };
}

#[macro_export]
macro_rules! impl_remote {
    ($name: ident, $remote_url: tt, $local_dir: expr, $file_name: tt, $file_type: tt) => {
        pub struct $name;

        impl $name {
            pub fn load_bytes() -> Result<Vec<u8>, crate::errors::ParameterError> {
                const METADATA: &'static str = include_str!(concat!($local_dir, $file_name, ".metadata"));

                let metadata: serde_json::Value =
                    serde_json::from_str(METADATA).expect("Metadata was not well-formatted");
                let expected_checksum: String = metadata[concat!($file_type, "_checksum")]
                    .as_str()
                    .expect("Failed to parse checksum")
                    .to_string();
                let expected_size: usize = metadata[concat!($file_type, "_size")]
                    .to_string()
                    .parse()
                    .expect("Failed to retrieve the file size");

                // Construct the versioned filename.
                let filename = match expected_checksum.get(0..7) {
                    Some(sum) => format!("{}.{}.{}", $file_name, $file_type, sum),
                    _ => concat!($file_name, $file_type).to_string(),
                };

                // Compose the correct file path for the parameter file.
                let mut file_path = std::path::PathBuf::from(file!());
                file_path.pop();
                file_path.push($local_dir);
                file_path.push(&filename);

                // Construct new parameters check.
                let parameters = crate::check_parameters::CheckParameters::new(
                    expected_checksum,
                    expected_size,
                    filename,
                    file_path,
                    String::from($remote_url),
                );

                // Compute parameters file bytes.
                parameters.load_bytes()
            }
        }

        paste::item! {
            #[cfg(test)]
            #[test]
            fn [< test_ $file_name _ $file_type >]() {
                assert!($name::load_bytes().is_ok());
            }
        }
    };
}
