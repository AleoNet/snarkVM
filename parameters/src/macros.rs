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
    ($name: ident, $test_name: ident, $remote_url: tt, $local_dir: expr, $fname: tt, $size: tt) => {

        pub struct $name;

        impl crate::traits::Parameter for $name {
            const CHECKSUM: &'static str = include_str!(concat!($local_dir, $fname, ".checksum"));
            const SIZE: u64 = $size;

            fn load_bytes() -> Result<Vec<u8>, crate::errors::ParameterError> {
                // Compose the correct file path for the parameter file.
                let filename = Self::versioned_filename();
                let mut file_path = std::path::PathBuf::from(file!());
                file_path.pop();
                file_path.push($local_dir);
                file_path.push(&filename);

                // Compute the relative path.
                let relative_path = if file_path.strip_prefix("parameters").is_ok() {
                    file_path.strip_prefix("parameters")?
                } else {
                    &file_path
                };

                // Compute the absolute path.
                let mut absolute_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
                absolute_path.push(&relative_path);

                let buffer = if relative_path.exists() {
                    // Attempts to load the parameter file locally with a relative path.
                    std::fs::read(relative_path)?
                } else if absolute_path.exists() {
                    // Attempts to load the parameter file locally with an absolute path.
                    std::fs::read(absolute_path)?
                } else {
                    // Downloads the missing parameters and stores it in the local directory for use.
                    eprintln!(
                        "\nWARNING - \"{}\" does not exist, downloading this file remotely and storing it locally. Please ensure \"{}\" is stored in {:?}.\n",
                        filename, filename, file_path
                    );
                    let output = Self::load_remote()?;
                    match Self::store_bytes(&output, &relative_path, &absolute_path, &file_path) {
                        Ok(()) => output,
                        Err(_) => {
                            eprintln!(
                                "\nWARNING - Failed to store \"{}\" locally. Please download this file manually and ensure it is stored in {:?}.\n",
                                filename, file_path
                            );
                            output
                        }
                    }
                };

                let checksum = checksum!(&buffer);
                match Self::CHECKSUM == checksum {
                    true => Ok(buffer),
                    false => checksum_error!(Self::CHECKSUM.into(), checksum),
                }
            }
        }

        impl $name {
            #[cfg(any(test, feature = "remote"))]
            pub fn load_remote() -> Result<Vec<u8>, crate::errors::ParameterError> {
                use crate::traits::Parameter;

                println!("{} - Downloading parameters...", module_path!());
                let mut buffer = vec![];
                let url = Self::remote_url();
                Self::remote_fetch(&mut buffer, &url)?;
                println!("\n{} - Download complete", module_path!());

                // Verify the checksum of the remote data before returning
                let checksum = checksum!(&buffer);
                match Self::CHECKSUM == checksum {
                    true => Ok(buffer),
                    false => checksum_error!(Self::CHECKSUM.into(), checksum),
                }
            }

            #[cfg(not(any(test, feature = "remote")))]
            pub fn load_remote() -> Result<Vec<u8>, crate::errors::ParameterError> {
                Err(crate::errors::ParameterError::RemoteFetchDisabled)
            }

            fn versioned_filename() -> String {
                use crate::traits::Parameter;

                match Self::CHECKSUM.get(0..7) {
                    Some(sum) => format!("{}-{}.params", $fname, sum),
                    _ => concat!($fname, ".params",).to_string()
                }
            }

            #[cfg(any(test, feature = "remote"))]
            fn remote_url() -> String {
                format!("{}/{}", $remote_url, Self::versioned_filename())
            }

            fn store_bytes(
                buffer: &[u8],
                relative_path: &std::path::Path,
                absolute_path: &std::path::Path,
                file_path: &std::path::Path,
            ) -> Result<(), crate::errors::ParameterError> {
                use snarkvm_utilities::Write;

                println!("{} - Storing parameters ({:?})", module_path!(), file_path);
                // Attempt to write the parameter buffer to a file.
                if let Ok(mut file) = std::fs::File::create(relative_path) {
                    file.write_all(&buffer)?;
                } else if let Ok(mut file) = std::fs::File::create(absolute_path) {
                    file.write_all(&buffer)?;
                }
                Ok(())
            }

            #[cfg(any(test, feature = "remote"))]
            fn remote_fetch(buffer: &mut Vec<u8>, url: &str) -> Result<(), crate::errors::ParameterError> {
                let mut easy = curl::easy::Easy::new();
                easy.url(url)?;
                easy.progress(true)?;
                easy.progress_function(|total_download, current_download, _, _| {
                    let percent = (current_download / total_download) * 100.0;
                    let size_in_megabytes = total_download as u64 / 1_048_576;
                    print!(
                        "\r{} - {:.2}% complete ({:#} MB total)",
                        module_path!(),
                        percent,
                        size_in_megabytes
                    );
                    true
                })?;

                let mut transfer = easy.transfer();
                transfer.write_function(|data| {
                    buffer.extend_from_slice(data);
                    Ok(data.len())
                })?;
                Ok(transfer.perform()?)
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
