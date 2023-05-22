// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

mod bytes;
mod parse;
mod serialize;

#[derive(Clone, PartialEq, Eq)]
pub struct Certificate<N: Network> {
    /// The certificate.
    certificate: marlin::Certificate<N::PairingCurve>,
}

impl<N: Network> Certificate<N> {
    /// Initializes a new certificate.
    pub(super) const fn new(certificate: marlin::Certificate<N::PairingCurve>) -> Self {
        Self { certificate }
    }

    /// Returns the certificate from the proving and verifying key.
    pub fn certify(
        function_name: &str,
        proving_key: &ProvingKey<N>,
        verifying_key: &VerifyingKey<N>,
    ) -> Result<Certificate<N>> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Compute the certificate.
        let certificate = Marlin::<N>::prove_vk(N::marlin_fs_parameters(), verifying_key, proving_key)?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Certified '{function_name}': {} ms", timer.elapsed().as_millis()).dimmed());

        Ok(Self::new(certificate))
    }

    /// Returns the certificate from the proving and verifying key.
    pub fn verify(
        &self,
        function_name: &str,
        assignment: &circuit::Assignment<N::Field>,
        verifying_key: &VerifyingKey<N>,
    ) -> bool {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Verify the certificate.
        match Marlin::<N>::verify_vk(N::marlin_fs_parameters(), assignment, verifying_key, self) {
            Ok(is_valid) => {
                #[cfg(feature = "aleo-cli")]
                {
                    let elapsed = timer.elapsed().as_millis();
                    println!("{}", format!(" • Verified certificate for '{function_name}': {elapsed} ms").dimmed());
                }

                is_valid
            }
            Err(error) => {
                #[cfg(feature = "aleo-cli")]
                println!("{}", format!(" • Certificate verification failed: {error}").dimmed());
                false
            }
        }
    }
}

impl<N: Network> Deref for Certificate<N> {
    type Target = marlin::Certificate<N::PairingCurve>;

    fn deref(&self) -> &Self::Target {
        &self.certificate
    }
}
