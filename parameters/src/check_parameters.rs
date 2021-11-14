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

use crate::errors::ParameterError;

use std::path::PathBuf;

pub struct CheckParameters {
    expected_checksum: String,
    expected_size: usize,
    file_name: String,
    file_path: PathBuf,
    remote_url: String,
}

impl CheckParameters {
    pub fn new(
        expected_checksum: String,
        expected_size: usize,
        file_name: String,
        file_path: PathBuf,
        remote_url: String,
    ) -> Self {
        Self {
            expected_checksum,
            expected_size,
            file_name,
            file_path,
            remote_url,
        }
    }

    fn check_bytes(&self, buffer: &Vec<u8>) -> Result<(), ParameterError> {
        // Ensure the size matches.
        if self.expected_size != buffer.len() {
            return Err(crate::errors::ParameterError::SizeMismatch(
                self.expected_size,
                buffer.len(),
            ));
        }

        // Ensure the checksum matches.
        let candidate_checksum = checksum!(buffer.as_slice());
        if self.expected_checksum != candidate_checksum {
            return checksum_error!(self.expected_checksum.clone(), candidate_checksum);
        }

        Ok(())
    }

    pub fn load_bytes(&self) -> Result<Vec<u8>, ParameterError> {
        // Attempts to load the parameter file locally with a path to the aleo directory.
        let buffer_unchecked = if self.file_path.exists() {
            std::fs::read(self.file_path.clone())?
        } else {
            Vec::new()
        };

        // Checks the size and checksum of the existing parameters file.
        if self.check_bytes(&buffer_unchecked).is_ok() {
            return Ok(buffer_unchecked);
        }

        // Downloads the missing parameters and stores it in the local directory for use.
        eprintln!(
            "\nWARNING - \"{}\" does not exist, downloading this file remotely and storing it locally. Please ensure \"{}\" is stored in {:?}.\n",
            self.file_name, self.file_name, self.file_path
        );

        let buffer = {
            // Load remote file
            cfg_if::cfg_if! {
                if #[cfg(not(feature = "wasm"))] {
                    #[cfg(not(feature = "no_std_out"))]
                    println!("{} - Downloading parameters...", module_path!());


                    let mut buffer = vec![];
                    Self::remote_fetch(&mut buffer, &format!("{}/{}", self.remote_url, self.file_name))?;

                    #[cfg(not(feature = "no_std_out"))]
                    println!("\n{} - Download complete", module_path!());

                    // Ensure the checksum matches.
                    let candidate_checksum = checksum!(&buffer);
                    if self.expected_checksum != candidate_checksum {
                        return checksum_error!(self.expected_checksum.clone(), candidate_checksum)
                    }

                    match Self::store_bytes(&buffer, &self.file_path) {
                        Ok(()) => buffer,
                        Err(_) => {
                            eprintln!(
                                "\nWARNING - Failed to store \"{}\" locally. Please download this file manually and ensure it is stored in {:?}.\n",
                                self.file_name, self.file_path
                            );
                            buffer
                        }
                    }
                } else if #[cfg(feature = "wasm")] {
                    let buffer = alloc::sync::Arc::new(parking_lot::RwLock::new(vec![]));
                    let url = self.remote_url.clone();

                    // NOTE(julesdesmit): I'm leaking memory here so that I can get a
                    // static reference to the url, which is needed to pass it into
                    // the local thread which downloads the file.
                    let url = Box::leak(url.into_boxed_str());

                    let buffer_clone = alloc::sync::Arc::downgrade(&buffer);
                    Self::remote_fetch(buffer_clone, url)?;

                    // Recover the bytes.
                    let buffer = alloc::sync::Arc::try_unwrap(buffer).unwrap();
                    let buffer = buffer.write().clone();

                    // Ensure the checksum matches.
                    let candidate_checksum = checksum!(&buffer);
                    if self.expected_checksum != candidate_checksum {
                        return checksum_error!(self.expected_checksum.clone(), candidate_checksum)
                    }

                    buffer
                } else {
                    return Err(crate::errors::ParameterError::RemoteFetchDisabled);
                }
            }
        };

        // Check the size and checksum of the parameters file.
        self.check_bytes(&buffer)?;

        Ok(buffer)
    }

    #[cfg(not(feature = "wasm"))]
    fn store_bytes(buffer: &[u8], file_path: &std::path::Path) -> Result<(), crate::errors::ParameterError> {
        use snarkvm_utilities::Write;

        // Hide compilation warning.
        let _ = file_path;

        #[cfg(not(feature = "no_std_out"))]
        println!("{} - Storing parameters ({:?})", module_path!(), file_path);

        // Attempt to write the parameter buffer to a file.
        if let Ok(mut file) = std::fs::File::create(file_path) {
            file.write_all(&buffer)?;
        }

        Ok(())
    }

    #[cfg(not(feature = "wasm"))]
    fn remote_fetch(buffer: &mut Vec<u8>, url: &str) -> Result<(), crate::errors::ParameterError> {
        let mut easy = curl::easy::Easy::new();
        easy.url(url)?;
        #[cfg(not(feature = "no_std_out"))]
        {
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
        }

        let mut transfer = easy.transfer();
        transfer.write_function(|data| {
            buffer.extend_from_slice(data);
            Ok(data.len())
        })?;
        Ok(transfer.perform()?)
    }

    #[cfg(feature = "wasm")]
    fn remote_fetch(
        buffer: alloc::sync::Weak<parking_lot::RwLock<Vec<u8>>>,
        url: &'static str,
    ) -> Result<(), crate::errors::ParameterError> {
        // NOTE(julesdesmit): We spawn a local thread here in order to be
        // able to accommodate the async syntax from reqwest.
        wasm_bindgen_futures::spawn_local(async move {
            let content = reqwest::get(url).await.unwrap().text().await.unwrap();

            let buffer = buffer.upgrade().unwrap();
            buffer.write().extend_from_slice(content.as_bytes());
            drop(buffer);
        });
        Ok(())
    }
}
