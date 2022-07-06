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
pub struct ProvingKey<N: Network> {
    /// The proving key for the function.
    proving_key: marlin::CircuitProvingKey<N::PairingCurve, marlin::MarlinHidingMode>,
}

impl<N: Network> ProvingKey<N> {
    /// Initializes a new proving key.
    pub(super) const fn new(proving_key: marlin::CircuitProvingKey<N::PairingCurve, marlin::MarlinHidingMode>) -> Self {
        Self { proving_key }
    }

    /// Returns a proof for the given assignment on the circuit.
    pub fn prove<R: Rng + CryptoRng>(
        &self,
        assignment: &circuit::Assignment<N::Field>,
        rng: &mut R,
    ) -> Result<Proof<N>> {
        let timer = std::time::Instant::now();
        let proof = Proof::new(Marlin::<N>::prove_batch(self, std::slice::from_ref(assignment), rng)?);
        println!("{}", format!(" • Called prover: {} ms", timer.elapsed().as_millis()).dimmed());
        Ok(proof)
    }
}

impl<N: Network> FromBytes for ProvingKey<N> {
    /// Reads the proving key from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let proving_key = FromBytes::read_le(&mut reader)?;
        Ok(Self { proving_key })
    }
}

impl<N: Network> ToBytes for ProvingKey<N> {
    /// Writes the proving key to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.proving_key.write_le(&mut writer)
    }
}

impl<N: Network> Deref for ProvingKey<N> {
    type Target = marlin::CircuitProvingKey<N::PairingCurve, marlin::MarlinHidingMode>;

    fn deref(&self) -> &Self::Target {
        &self.proving_key
    }
}
