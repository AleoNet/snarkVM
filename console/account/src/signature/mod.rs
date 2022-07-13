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

mod bytes;
mod sign;

#[cfg(feature = "compute_key")]
use crate::ComputeKey;
#[cfg(feature = "private_key")]
use crate::PrivateKey;

use crate::address::Address;
use snarkvm_console_network::prelude::*;
use snarkvm_console_types::{Field, Scalar};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Signature<N: Network> {
    /// The verifier challenge to check against.
    challenge: Scalar<N>,
    /// The prover response to the challenge.
    response: Scalar<N>,
    /// The compute key of the prover.
    compute_key: ComputeKey<N>,
}

impl<N: Network> From<(Scalar<N>, Scalar<N>, ComputeKey<N>)> for Signature<N> {
    /// Derives the account signature from a tuple `(challenge, response, compute_key)`.
    fn from((challenge, response, compute_key): (Scalar<N>, Scalar<N>, ComputeKey<N>)) -> Self {
        Self { challenge, response, compute_key }
    }
}

impl<N: Network> From<&(Scalar<N>, Scalar<N>, ComputeKey<N>)> for Signature<N> {
    /// Derives the account signature from a tuple `(challenge, response, compute_key)`.
    fn from((challenge, response, compute_key): &(Scalar<N>, Scalar<N>, ComputeKey<N>)) -> Self {
        Self { challenge: *challenge, response: *response, compute_key: *compute_key }
    }
}

impl<N: Network> Signature<N> {
    /// Returns the verifier challenge.
    pub const fn challenge(&self) -> Scalar<N> {
        self.challenge
    }

    /// Returns the prover response.
    pub const fn response(&self) -> Scalar<N> {
        self.response
    }

    /// Returns the signer compute key.
    pub const fn compute_key(&self) -> ComputeKey<N> {
        self.compute_key
    }

    /// Returns the signer address.
    pub fn signer(&self) -> Result<Address<N>> {
        Address::try_from(self.compute_key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_from() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for i in 0..ITERATIONS {
            // Sample an address and a private key.
            let private_key = PrivateKey::<CurrentNetwork>::new(rng)?;
            let address = Address::try_from(&private_key)?;

            // Generate a signature.
            let message: Vec<_> = (0..i).map(|_| Uniform::rand(rng)).collect();
            let signature = Signature::sign(&private_key, &message, rng)?;
            assert!(signature.verify(&address, &message));

            // Check that the signature can be reconstructed from its parts.
            let candidate = Signature::from((signature.challenge(), signature.response(), signature.compute_key()));
            assert_eq!(signature, candidate);
        }
        Ok(())
    }
}
