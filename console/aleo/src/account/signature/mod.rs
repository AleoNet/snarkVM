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

use crate::{Address, ComputeKey, Network, PrivateKey};
use snarkvm_curves::{AffineCurve, ProjectiveCurve};
use snarkvm_fields::ToConstraintField;
use snarkvm_utilities::{
    io::{Read, Result as IoResult, Write},
    FromBytes,
    ToBytes,
};

use anyhow::Result;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Signature<N: Network> {
    /// The verifier challenge to check against.
    challenge: N::Scalar,
    /// The prover response to the challenge.
    response: N::Scalar,
    /// The compute key of the prover.
    compute_key: ComputeKey<N>,
}

impl<N: Network> Signature<N> {
    /// Returns a signature `(challenge, response, compute_key)` for a given message and randomizer, where:
    ///     challenge := HashToScalar(address, G^randomizer, message)
    ///     response := randomizer - challenge * private_key.sk_sig()
    pub fn sign(private_key: &PrivateKey<N>, message: &[bool], randomizer: N::Scalar) -> Result<Self> {
        // Compute G^randomizer.
        let g_r = N::g_scalar_multiply(&randomizer).to_affine();

        // Derive the compute key from the private key.
        let compute_key = ComputeKey::try_from(private_key)?;
        // Derive the address from the compute key.
        let address = Address::try_from(compute_key)?;

        // Construct the hash input (address, G^randomizer, message).
        let mut preimage = vec![];
        preimage.extend_from_slice(&address.to_x_coordinate().to_field_elements()?);
        preimage.extend_from_slice(&g_r.to_x_coordinate().to_field_elements()?);
        preimage.push(N::Field::from(message.len() as u128));
        preimage.extend_from_slice(&message.to_field_elements()?);

        // Compute the verifier challenge.
        let challenge = N::hash_to_scalar_psd8(&preimage)?;

        // Compute the prover response.
        let response = randomizer - (challenge * private_key.sk_sig());

        // Output the signature.
        Ok(Self { challenge, response, compute_key })
    }

    ///
    /// Verifies (challenge == challenge') && (address == address') where:
    ///     challenge' := HashToScalar(address', G^response pk_sig^challenge, message)
    ///
    pub fn verify(&self, address: &Address<N>, message: &[bool]) -> Result<bool> {
        // Compute the candidate public key as (G^sk_sig G^r_sig G^sk_prf).
        let candidate_address = Address::try_from(self.compute_key)?;

        // Compute pk_sig_challenge := pk_sig^challenge.
        let pk_sig_challenge = self.compute_key.pk_sig().to_projective() * self.challenge;

        // Compute G^randomizer := G^response pk_sig_challenge.
        let g_randomizer = (N::g_scalar_multiply(&self.response) + pk_sig_challenge).to_affine();

        // Construct the hash input (address', G^randomizer, message).
        let mut preimage = vec![];
        preimage.extend_from_slice(&candidate_address.to_x_coordinate().to_field_elements()?);
        preimage.extend_from_slice(&g_randomizer.to_x_coordinate().to_field_elements()?);
        preimage.push(N::Field::from(message.len() as u128));
        preimage.extend_from_slice(&message.to_field_elements()?);

        // Hash to derive the verifier challenge.
        let candidate_challenge = N::hash_to_scalar_psd8(&preimage)?;

        Ok(self.challenge == candidate_challenge && *address == candidate_address)
    }

    /// Returns the verifier challenge.
    pub const fn challenge(&self) -> &N::Scalar {
        &self.challenge
    }

    /// Returns the prover response.
    pub const fn response(&self) -> &N::Scalar {
        &self.response
    }

    /// Returns the compute key.
    pub const fn compute_key(&self) -> &ComputeKey<N> {
        &self.compute_key
    }
}

impl<N: Network> FromBytes for Signature<N> {
    #[inline]
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        let challenge = N::Scalar::read_le(&mut reader)?;
        let response = N::Scalar::read_le(&mut reader)?;
        let compute_key = ComputeKey::read_le(&mut reader)?;
        Ok(Self { challenge, response, compute_key })
    }
}

impl<N: Network> ToBytes for Signature<N> {
    #[inline]
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.challenge.write_le(&mut writer)?;
        self.response.write_le(&mut writer)?;
        self.compute_key.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Testnet3;
    use snarkvm_utilities::{test_crypto_rng, ToBits, UniformRand};

    type CurrentNetwork = Testnet3;

    fn check_sign_and_verify(message: &[bool]) -> Result<()> {
        // Generate an address and a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
        let address = Address::try_from(&private_key)?;

        // Generate a signature.
        let randomizer = UniformRand::rand(&mut test_crypto_rng());
        let signature = Signature::sign(&private_key, message, randomizer)?;
        assert!(signature.verify(&address, message).unwrap());
        Ok(())
    }

    fn check_sign_and_verify_fails(message: &[bool], bad_message: &[bool]) -> Result<()> {
        // Generate an address and a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
        let address = Address::try_from(&private_key)?;

        // Generate a signature.
        let randomizer = UniformRand::rand(&mut test_crypto_rng());
        let signature = Signature::sign(&private_key, message, randomizer)?;
        assert!(!signature.verify(&address, bad_message).unwrap());
        Ok(())
    }

    #[test]
    fn test_sign_and_verify() -> Result<()> {
        let message = "Hi, I am an Aleo signature!";
        check_sign_and_verify(&message.as_bytes().to_bits_le())?;
        check_sign_and_verify_fails(&message.as_bytes().to_bits_le(), &b"Bad message".to_bits_le())
    }
}
