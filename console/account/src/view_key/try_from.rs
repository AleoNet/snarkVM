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

#[cfg(feature = "private_key")]
impl<N: Network> TryFrom<PrivateKey<N>> for ViewKey<N> {
    type Error = Error;

    /// Initializes a new account view key from an account private key.
    fn try_from(private_key: PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

#[cfg(feature = "private_key")]
impl<N: Network> TryFrom<&PrivateKey<N>> for ViewKey<N> {
    type Error = Error;

    /// Initializes a new account view key from an account private key.
    fn try_from(private_key: &PrivateKey<N>) -> Result<Self, Self::Error> {
        // Derive the compute key.
        let compute_key = ComputeKey::try_from(private_key)?;
        // Compute view_key := sk_sig + r_sig + sk_prf.
        Ok(Self(private_key.sk_sig() + private_key.r_sig() + compute_key.sk_prf()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_try_from() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new compute key and view key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let compute_key = ComputeKey::try_from(private_key)?;
            let view_key = ViewKey::try_from(private_key)?;

            // Check that the view key matches.
            // Compute view_key := sk_sig + r_sig + sk_prf.
            let candidate = ViewKey(private_key.sk_sig() + private_key.r_sig() + compute_key.sk_prf());
            assert_eq!(view_key, candidate);
        }
        Ok(())
    }
}
