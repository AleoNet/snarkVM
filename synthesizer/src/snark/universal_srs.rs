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

#[derive(Clone)]
pub struct UniversalSRS<N: Network> {
    /// The universal SRS parameter.
    srs: Arc<OnceCell<marlin::UniversalSRS<N::PairingCurve>>>,
}

impl<N: Network> UniversalSRS<N> {
    /// Initializes the universal SRS.
    pub fn load() -> Result<Self> {
        Ok(Self { srs: Arc::new(OnceCell::new()) })
    }

    /// Returns the circuit proving and verifying key.
    pub fn to_circuit_key(
        &self,
        function_name: &Identifier<N>,
        assignment: &circuit::Assignment<N::Field>,
    ) -> Result<(ProvingKey<N>, VerifyingKey<N>)> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        let (proving_key, verifying_key) = Marlin::<N>::circuit_setup(self, assignment)?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Built '{function_name}' (in {} ms)", timer.elapsed().as_millis()).dimmed());

        Ok((ProvingKey::new(Arc::new(proving_key)), VerifyingKey::new(Arc::new(verifying_key))))
    }
}

impl<N: Network> FromBytes for UniversalSRS<N> {
    /// Reads the universal SRS from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        Ok(Self { srs: Arc::new(OnceCell::with_value(FromBytes::read_le(&mut reader)?)) })
    }
}

impl<N: Network> ToBytes for UniversalSRS<N> {
    /// Writes the universal SRS to a buffer.
    fn write_le<W: Write>(&self, writer: W) -> IoResult<()> {
        self.deref().write_le(writer)
    }
}

impl<N: Network> Deref for UniversalSRS<N> {
    type Target = marlin::UniversalSRS<N::PairingCurve>;

    #[allow(clippy::let_and_return)]
    fn deref(&self) -> &Self::Target {
        self.srs.get_or_init(|| {
            #[cfg(feature = "aleo-cli")]
            let timer = std::time::Instant::now();

            // Load the universal SRS.
            let universal_srs = marlin::UniversalSRS::load().expect("Failed to load the universal SRS");

            #[cfg(feature = "aleo-cli")]
            println!("{}", format!(" • Loaded universal setup (in {} ms)", timer.elapsed().as_millis()).dimmed());

            universal_srs
        })
    }
}
