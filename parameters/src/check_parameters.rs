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

use std::{
    fs::create_dir_all,
    io::Read,
    path::{Path, PathBuf},
};

pub struct CheckParameters {
    filename: String,
    filepath: PathBuf,
    checksum: String,
    url: String,
}

impl CheckParameters {
    pub fn new(filename: &str, filepath: PathBuf, url: &str, checksum: &str) -> Self {
        Self {
            filename: filename.to_string(),
            filepath,
            checksum: checksum.to_string(),
            url: url.to_string(),
        }
    }

    fn parameters_path_from_env(&self) -> Result<PathBuf, ParameterError> {
        let path = option_env!("ALEO_PROOFS_PARAMETER_CACHE")
            .map(|name| Path::new(name).to_path_buf())
            .unwrap_or_else(|| self.filepath.clone());

        if !path.exists() || !path.is_dir() {
            create_dir_all(path.clone())
                .map(|_| path.to_path_buf())
                .map_err(|err| ParameterError::Message(format!("{}", err)))
        } else {
            Ok(path.to_path_buf())
        }
    }

    fn checksum(message: &[u8]) -> String {
        hex::encode(snarkvm_algorithms::crh::sha256::sha256(message))
    }

    pub fn load_bytes(&self) -> Result<Vec<u8>, ParameterError> {
        // Compose the correct file path for the parameter file.
        let parameters_path = self.parameters_path_from_env()?;
        let file_path = parameters_path.join(self.versioned_filename());

        // Attempts to load the parameter file locally.
        let content = std::fs::File::open(file_path.clone())
            .map(|mut file| {
                let mut buffer = Vec::new();
                file.read_to_end(&mut buffer).unwrap_or(0);
                buffer
            })
            .unwrap_or(Vec::new());

        if Self::checksum(content.as_ref()) != self.checksum {
            // Downloads the missing parameters and stores it in the local directory for use.
            eprintln!(
                "\nWARNING - \"{}\" does not exist, downloading this file remotely and storing it locally. Please ensure \"{}\" is stored in {:?}.\n",
                self.filename, self.filename, file_path
            );

            // Load remote file
            cfg_if::cfg_if! {
                if #[cfg(not(feature = "wasm"))] {
                    #[cfg(not(feature = "no_std_out"))]
                    println!("{} - Downloading parameters...", self.remote_url());

                    let mut buffer = Vec::new();
                    self.remote_fetch(&mut buffer)?;

                    #[cfg(not(feature = "no_std_out"))]
                    println!("{} - Download complete", self.remote_url());

                    // Ensure the checksum matches.
                    let candidate_checksum = checksum!(&buffer);
                    if self.checksum != candidate_checksum {
                        return checksum_error!(self.checksum.clone(), candidate_checksum)
                    }

                    match Self::store_bytes(&buffer, &file_path) {
                        Ok(()) => Ok(buffer),
                        Err(_) => {
                            eprintln!(
                                "\nWARNING - Failed to store \"{}\" locally. Please download this file manually and ensure it is stored in {:?}.\n",
                                self.filename, file_path
                            );
                            Ok(buffer)
                        }
                    }

                } else if #[cfg(feature = "wasm")] {
                    let buffer = alloc::sync::Arc::new(parking_lot::RwLock::new(vec![]));
                    let url = self.remote_url;

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
                    if expected_checksum != candidate_checksum {
                        return checksum_error!(expected_checksum, candidate_checksum)
                    }

                    Ok(buffer)
                } else {
                    return Err(crate::errors::ParameterError::RemoteFetchDisabled);
                }
            }
        } else {
            Ok(content)
        }
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
        // else {} // todo (@howardwu) should we throw an error here?

        Ok(())
    }

    fn versioned_filename(&self) -> String {
        self.checksum
            .get(0..7)
            .map(|x| format!("{}-{}.params", self.filename, x))
            .unwrap_or(self.filename.to_string() + ".params")
    }

    fn remote_url(&self) -> String {
        format!("{}/{}", self.url, self.versioned_filename())
    }

    #[cfg(not(feature = "wasm"))]
    fn remote_fetch(&self, buffer: &mut Vec<u8>) -> Result<(), ParameterError> {
        let mut easy = curl::easy::Easy::new();
        easy.url(self.remote_url().as_str())?;
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
        self,
        buffer: alloc::sync::Weak<parking_lot::RwLock<Vec<u8>>>,
    ) -> Result<(), crate::errors::ParameterError> {
        // NOTE(julesdesmit): We spawn a local thread here in order to be
        // able to accommodate the async syntax from reqwest.
        wasm_bindgen_futures::spawn_local(async move {
            let content = reqwest::get(self.remote_url().as_str())
                .await
                .unwrap()
                .text()
                .await
                .unwrap();

            let buffer = buffer.upgrade().unwrap();
            buffer.write().extend_from_slice(content.as_bytes());
            drop(buffer);
        });
        Ok(())
    }
}

// #[cfg(test)]
// mod tests {
//     use super::CheckParameters;
//
//     #[test]
//     fn test_posw_snark_param() {
//         let checksum = include_str!(concat!("./testnet1/", "posw_snark_pk", ".checksum"));
//         let filename = "posw_snark_pk";
//         let url = "https://snarkos-testnet.s3-us-west-2.amazonaws.com";
//         let para = CheckParameters::new(filename, url, checksum);
//
//         assert!(para.load_bytes().is_ok());
//     }
// }
