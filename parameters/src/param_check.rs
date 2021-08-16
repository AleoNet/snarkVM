use crate::errors::ParameterError;
use std::path::{Path, PathBuf};
use std::fs::create_dir_all;
use std::io::{Read, Write};

pub struct ParamCheck {
    checksum: String,
    url: String,
    fname: String,
}

impl ParamCheck {
    pub fn new(fname: &str, url: &str, checksum: &str) -> Self {
        Self {
            checksum: checksum.to_string(),
            url: url.to_string(),
            fname: fname.to_string(),
        }
    }

    fn para_path_from_env() -> Result<PathBuf, ParameterError> {
        let p = option_env!("ALEO_PROOFS_PARAMETER_CACHE").map(|p| Path::new(p).to_path_buf())
            .unwrap_or_else(|| std::env::temp_dir().join("aleo-proof-parameters"));
        if !p.exists() || !p.is_dir() {
            create_dir_all(p.clone()).map(|_| p.to_path_buf()).map_err(|e| ParameterError::Message(format!("{}", e)))
        } else {
            Ok(p.to_path_buf())
        }
    }

    fn checksum(msg: &[u8]) -> String {
        hex::encode(snarkvm_algorithms::crh::sha256::sha256(msg))
    }

    pub fn load_bytes(&self) -> Result<Vec<u8>, ParameterError> {
        let para_path = Self::para_path_from_env()?;
        let para_file = para_path.join(self.versioned_filename());
        let content = std::fs::File::open(para_file.clone()).map(|mut x| {
            let mut buf = Vec::new();
            x.read_to_end(&mut buf).unwrap_or(0);
            buf
        }).unwrap_or(Vec::new());

        if Self::checksum(content.as_ref()) != self.checksum {
            let buf = self.load_remote()?;
            match std::fs::File::create(para_file).map(|mut f| {
                f.write_all(buf.as_ref()).unwrap_or(())
            }) {
                Ok(_) => {},
                Err(e) => {
                    tracing::error!("Cannot store the data of {} caused by the {}", self.versioned_filename(), format!("{:?}", e));
                },
            }
            Ok(buf)
        } else {
            Ok(content)
        }
    }

    fn load_remote(&self) ->  Result<Vec<u8>, ParameterError> {
        println!("{} - Downloading parameters...", self.remote_url());
        let mut buffer = Vec::new();
        self.remote_fetch(&mut buffer)?;
        println!("{} - Download complete", self.remote_url());

        // Verify the checksum of the remote data before returning
        let checksum = Self::checksum(buffer.as_slice());
        match self.checksum == checksum {
            true => Ok(buffer),
            false => Err(ParameterError::ChecksumMismatch(self.checksum.clone(), checksum.clone()))
        }
    }

    fn versioned_filename(&self) -> String {
        self.checksum.get(0..7).map(|x| format!("{}-{}.params", self.fname, x))
            .unwrap_or(self.fname.to_string() + ".params")
    }

    fn remote_url(&self) -> String {
        format!("{}/{}", self.url, self.versioned_filename())
    }

    fn remote_fetch(&self, buf: &mut Vec<u8>) -> Result<(), ParameterError> {
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
            buf.extend_from_slice(data);
            Ok(data.len())
        })?;
        Ok(transfer.perform()?)
    }
}

#[cfg(test)]
mod tests {
    use super::ParamCheck;

    #[test]
    fn test_posw_snark_param() {
        let checksum = include_str!(concat!("./testnet1/", "posw_snark_pk", ".checksum"));
        let filename = "posw_snark_pk";
        let url = "https://snarkos-testnet.s3-us-west-2.amazonaws.com";
        let para = ParamCheck::new(filename, url, checksum);

        assert!(para.load_bytes().is_ok());
    }
}
