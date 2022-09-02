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

#[derive(Clone, Debug)]
pub struct ProverPuzzleSolution<N: Network> {
    pub address: Address<N>,
    pub nonce: u64,
    pub commitment: Commitment<N::PairingCurve>,
    pub proof: Proof<N::PairingCurve>,
}

impl<N: Network> ProverPuzzleSolution<N> {
    pub fn verify(
        &self,
        vk: &CoinbasePuzzleVerifyingKey<N>,
        epoch_info: &EpochInfo,
        epoch_challenge: &EpochChallenge<N>,
    ) -> Result<bool> {
        if self.proof.is_hiding() {
            return Ok(false);
        }

        let polynomial =
            CoinbasePuzzle::sample_solution_polynomial(epoch_challenge, epoch_info, &self.address, self.nonce)?;
        let point = hash_commitment(&self.commitment);
        let epoch_challenge_eval = epoch_challenge.epoch_polynomial.evaluate(point);
        let polynomial_eval = polynomial.evaluate(point);
        let product_eval = epoch_challenge_eval * polynomial_eval;
        Ok(KZG10::check(vk, &self.commitment, point, product_eval, &self.proof)?)
    }
}

impl<N: Network> Eq for ProverPuzzleSolution<N> {}

impl<N: Network> PartialEq for ProverPuzzleSolution<N> {
    /// Implements the `Eq` trait for the ProverPuzzleSolution.
    fn eq(&self, other: &Self) -> bool {
        self.address == other.address
            && self.nonce == other.nonce
            && self.commitment == other.commitment
            && self.proof == other.proof
    }
}

// TODO (raychu86): Use derive Hash. It seems commitment and proof do not derive it properly.
impl<N: Network> core::hash::Hash for ProverPuzzleSolution<N> {
    /// Implements the `Hash` trait for the ProverPuzzleSolution.
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.address.hash(state);
        self.nonce.hash(state);
        self.commitment.0.hash(state);
        self.proof.w.hash(state);
        self.proof.random_v.hash(state);
    }
}

impl<N: Network> ToBytes for ProverPuzzleSolution<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.address.write_le(&mut writer)?;
        self.nonce.write_le(&mut writer)?;
        self.commitment.write_le(&mut writer)?;
        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for ProverPuzzleSolution<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let address: Address<N> = FromBytes::read_le(&mut reader)?;
        let nonce = u64::read_le(&mut reader)?;
        let commitment = Commitment::read_le(&mut reader)?;
        let proof = Proof::read_le(&mut reader)?;

        Ok(Self { address, nonce, commitment, proof })
    }
}
