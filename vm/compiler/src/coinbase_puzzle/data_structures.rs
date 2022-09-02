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

use crate::coinbase_puzzle::{hash_commitment, CoinbasePuzzle};
use console::{account::Address, prelude::*};
use snarkvm_algorithms::{
    fft::{DensePolynomial, EvaluationDomain},
    polycommit::kzg10::{Commitment, LagrangeBasis, Powers, Proof, VerifierKey, KZG10},
};
use snarkvm_curves::PairingEngine;
use snarkvm_utilities::{FromBytes, ToBytes};

use anyhow::Result;
use std::{
    borrow::Cow,
    collections::BTreeMap,
    io::{Read, Result as IoResult, Write},
};

pub type CoinbasePuzzleVerifyingKey<N> = VerifierKey<<N as Environment>::PairingCurve>;

#[derive(Clone, Debug)]
pub struct CoinbasePuzzleProvingKey<N: Network> {
    /// The key used to commit to polynomials.
    pub powers_of_beta_g: Vec<<N::PairingCurve as PairingEngine>::G1Affine>,

    /// The key used to commit to polynomials in Lagrange basis.
    pub lagrange_bases_at_beta_g: BTreeMap<usize, Vec<<N::PairingCurve as PairingEngine>::G1Affine>>,

    pub vk: VerifierKey<N::PairingCurve>,
}

impl<N: Network> CoinbasePuzzleProvingKey<N> {
    /// Obtain powers for the underlying KZG10 construction
    pub fn powers(&self) -> Powers<N::PairingCurve> {
        Powers {
            powers_of_beta_g: self.powers_of_beta_g.as_slice().into(),
            powers_of_beta_times_gamma_g: Cow::Owned(vec![]),
        }
    }

    /// Obtain elements of the SRS in the lagrange basis powers.
    pub fn lagrange_basis(
        &self,
        domain: EvaluationDomain<<N::PairingCurve as PairingEngine>::Fr>,
    ) -> Option<LagrangeBasis<N::PairingCurve>> {
        self.lagrange_bases_at_beta_g.get(&domain.size()).map(|basis| LagrangeBasis {
            lagrange_basis_at_beta_g: Cow::Borrowed(basis),
            powers_of_beta_times_gamma_g: Cow::Owned(vec![]),
            domain,
        })
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EpochInfo {
    pub epoch_number: u64,
    // TODO (raychu86): Add additional elements to pin the epoch info to a specific block.
}

impl EpochInfo {
    pub fn to_bytes_le(&self) -> [u8; 8] {
        self.epoch_number.to_le_bytes()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochChallenge<N: Network> {
    pub epoch_polynomial: DensePolynomial<<N::PairingCurve as PairingEngine>::Fr>,
}

impl<N: Network> EpochChallenge<N> {
    pub fn degree(&self) -> usize {
        self.epoch_polynomial.degree()
    }
}

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

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CombinedPuzzleSolution<N: Network> {
    pub individual_puzzle_solutions: Vec<(Address<N>, u64, Commitment<N::PairingCurve>)>,
    pub proof: Proof<N::PairingCurve>,
}

impl<N: Network> CombinedPuzzleSolution<N> {
    pub fn new(
        individual_puzzle_solutions: Vec<(Address<N>, u64, Commitment<N::PairingCurve>)>,
        proof: Proof<N::PairingCurve>,
    ) -> Self {
        Self { individual_puzzle_solutions, proof }
    }
}

impl<N: Network> ToBytes for CombinedPuzzleSolution<N> {
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        (self.individual_puzzle_solutions.len() as u32).write_le(&mut writer)?;

        for individual_puzzle_solution in &self.individual_puzzle_solutions {
            individual_puzzle_solution.0.write_le(&mut writer)?;
            individual_puzzle_solution.1.write_le(&mut writer)?;
            individual_puzzle_solution.2.write_le(&mut writer)?;
        }

        self.proof.write_le(&mut writer)
    }
}

impl<N: Network> FromBytes for CombinedPuzzleSolution<N> {
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let individual_puzzle_solutions_len: u32 = FromBytes::read_le(&mut reader)?;

        let mut individual_puzzle_solutions = Vec::with_capacity(individual_puzzle_solutions_len as usize);
        for _ in 0..individual_puzzle_solutions_len {
            let address: Address<N> = FromBytes::read_le(&mut reader)?;
            let nonce: u64 = FromBytes::read_le(&mut reader)?;
            let commitment: Commitment<N::PairingCurve> = FromBytes::read_le(&mut reader)?;
            individual_puzzle_solutions.push((address, nonce, commitment));
        }

        let proof = Proof::read_le(&mut reader)?;

        Ok(Self { individual_puzzle_solutions, proof })
    }
}

impl<N: Network> Serialize for CombinedPuzzleSolution<N> {
    /// Serializes the CombinedPuzzleSolution to a JSON-string or buffer.
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // match serializer.is_human_readable() {
        //     true => {
        //         let mut combined_puzzle_solution = serializer.serialize_struct("CombinedPuzzleSolution", 2)?;
        //         combined_puzzle_solution
        //             .serialize_field("individual_puzzle_solutions", &self.individual_puzzle_solutions)?;
        //         combined_puzzle_solution.serialize_field("proof", &self.proof)?;
        //         combined_puzzle_solution.end()
        //     }
        //     false => ToBytesSerializer::serialize_with_size_encoding(self, serializer),
        // }

        unimplemented!()
    }
}

impl<'de, N: Network> Deserialize<'de> for CombinedPuzzleSolution<N> {
    /// Deserializes the CombinedPuzzleSolution from a JSON-string or buffer.
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // match deserializer.is_human_readable() {
        //     true => {
        //         let combined_puzzle_solution = serde_json::Value::deserialize(deserializer)?;
        //         Ok(Self::new(
        //             serde_json::from_value(combined_puzzle_solution["individual_puzzle_solutions"].clone())
        //                 .map_err(de::Error::custom)?,
        //             serde_json::from_value(combined_puzzle_solution["proof"].clone()).map_err(de::Error::custom)?,
        //         )
        //         .map_err(de::Error::custom)?)
        //     }
        //     false => {
        //         FromBytesDeserializer::<Self>::deserialize_with_size_encoding(deserializer, "combined puzzle solution")
        //     }
        // }

        unimplemented!()
    }
}

impl<N: Network> FromStr for CombinedPuzzleSolution<N> {
    type Err = Error;

    /// Initializes the block from a JSON-string.
    fn from_str(combined_puzzle_solution: &str) -> Result<Self, Self::Err> {
        Ok(serde_json::from_str(combined_puzzle_solution)?)
    }
}

impl<N: Network> Debug for CombinedPuzzleSolution<N> {
    /// Prints the CombinedPuzzleSolution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for CombinedPuzzleSolution<N> {
    /// Displays the CombinedPuzzleSolution as a JSON-string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", serde_json::to_string(self).map_err::<fmt::Error, _>(ser::Error::custom)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_serde_json() -> Result<()> {
        // TODO (raychu86): Implement this.
        Ok(())
    }

    #[test]
    fn test_bincode() -> Result<()> {
        // TODO (raychu86): Implement this.

        Ok(())
    }
}
