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
        function_name: &Identifier<N>,
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
        function_name: &Identifier<N>,
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
                    println!("{}", format!(" • Verified certificate for '{function_name}': {} ms", elapsed).dimmed());
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

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;

    pub(super) fn sample_certificate() -> Certificate<CurrentNetwork> {
        static INSTANCE: OnceCell<Certificate<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                // Sample a circuit.
                let (function_name, proving_key, verifying_key) = crate::process::test_helpers::sample_key();
                // Return the certificate.
                Certificate::certify(&function_name, &proving_key, &verifying_key).unwrap()
            })
            .clone()
    }
}
