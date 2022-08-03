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

impl<N: Network> Stack<N> {
    /// Synthesizes and inserts the 'credits.aleo' circuit keys.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn setup_credits_program<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &mut self,
        rng: &mut R,
    ) -> Result<()> {
        // If the program is the 'credits.aleo' program, synthesize the keys.
        if *self.program.id() == ProgramID::from_str("credits.aleo")? {
            // Synthesize the 'credits.aleo' circuit keys.
            for function_name in self.program.functions().keys() {
                self.synthesize_key::<A, _>(function_name, rng)?;
            }
        }
        Ok(())
    }

    /// Loads and inserts the credits program circuit keys.
    #[inline]
    pub(crate) fn load_credits_program(&mut self) -> Result<()> {
        // If the program is the 'credits.aleo' program, load the keys.
        if *self.program.id() == ProgramID::from_str("credits.aleo")? {
            // Synthesize the 'credits.aleo' circuit keys.
            for function_name in self.program.functions().keys() {
                // TODO (howardwu): Abstract this into the `Network` trait.
                // Load the proving and verifying key bytes.
                let (proving_key, verifying_key) = snarkvm_parameters::testnet3::TESTNET3_CREDITS_PROGRAM
                    .get(&function_name.to_string())
                    .ok_or_else(|| anyhow!("Circuit keys for credits.aleo/{function_name}' not found"))?;

                // Insert the proving and verifying key.
                self.insert_proving_key(function_name, ProvingKey::from_bytes_le(proving_key)?);
                self.insert_verifying_key(function_name, VerifyingKey::from_bytes_le(verifying_key)?);
            }
        }
        Ok(())
    }
}
