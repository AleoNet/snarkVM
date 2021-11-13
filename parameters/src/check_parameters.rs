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
    io::{Read, Write},
    path::{Path, PathBuf},
};

pub struct CheckParameters {
    checksum: String,
    url: String,
    filename: String,
}

impl CheckParameters {
    pub fn new(filename: &str, url: &str, checksum: &str) -> Self {
        Self {
            checksum: checksum.to_string(),
            url: url.to_string(),
            filename: filename.to_string(),
        }
    }

    fn parameters_path_from_env() -> Result<PathBuf, ParameterError> {
        let path = option_env!("ALEO_PROOFS_PARAMETER_CACHE")
            .map(|name| Path::new(name).to_path_buf())
            .unwrap_or_else(|| std::env::temp_dir().join("aleo-proof-parameters"));
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
        let parameters_path = Self::parameters_path_from_env()?;
        let parameters_file = parameters_path.join(self.versioned_filename());
        let content = std::fs::File::open(parameters_file.clone())
            .map(|mut file| {
                let mut buffer = Vec::new();
                file.read_to_end(&mut buffer).unwrap_or(0);
                buffer
            })
            .unwrap_or(Vec::new());

        if Self::checksum(content.as_ref()) != self.checksum {
            let buffer = self.load_remote()?;
            match std::fs::File::create(parameters_file).map(|mut file| file.write_all(buffer.as_ref()).unwrap_or(())) {
                Ok(_) => {}
                Err(e) => {
                    tracing::error!(
                        "Cannot store the data of {} caused by the {}",
                        self.versioned_filename(),
                        format!("{:?}", e)
                    );
                }
            }
            Ok(buffer)
        } else {
            Ok(content)
        }
    }

    fn load_remote(&self) -> Result<Vec<u8>, ParameterError> {
        println!("{} - Downloading parameters...", self.remote_url());
        let mut buffer = Vec::new();
        self.remote_fetch(&mut buffer)?;
        println!("{} - Download complete", self.remote_url());

        // Verify the checksum of the remote data before returning
        let checksum = Self::checksum(buffer.as_slice());
        match self.checksum == checksum {
            true => Ok(buffer),
            false => Err(ParameterError::ChecksumMismatch(
                self.checksum.clone(),
                checksum.clone(),
            )),
        }
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

    fn remote_fetch(&self, buffer: &mut Vec<u8>) -> Result<(), ParameterError> {
        let mut easy = curl::easy::Easy::new();
        easy.url(self.remote_url().as_str())?;
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
mod tests {
    use super::CheckParameters;

    #[test]
    fn test_posw_snark_param() {
        let checksum = include_str!(concat!("./testnet1/", "posw_snark_pk", ".checksum"));
        let filename = "posw_snark_pk";
        let url = "https://snarkos-testnet.s3-us-west-2.amazonaws.com";
        let para = CheckParameters::new(filename, url, checksum);

        assert!(para.load_bytes().is_ok());
    }
}
