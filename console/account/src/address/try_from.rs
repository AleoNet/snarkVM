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
impl<N: Network> TryFrom<PrivateKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account private key.
    fn try_from(private_key: PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

#[cfg(feature = "private_key")]
impl<N: Network> TryFrom<&PrivateKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account private key.
    fn try_from(private_key: &PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(ComputeKey::try_from(private_key)?)
    }
}

#[cfg(feature = "compute_key")]
impl<N: Network> TryFrom<ComputeKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account compute key.
    fn try_from(compute_key: ComputeKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&compute_key)
    }
}

#[cfg(feature = "compute_key")]
impl<N: Network> TryFrom<&ComputeKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account compute key.
    fn try_from(compute_key: &ComputeKey<N>) -> Result<Self, Self::Error> {
        // Compute pk_prf := G^sk_prf.
        let pk_prf = N::g_scalar_multiply(&compute_key.sk_prf());
        // Compute the address := pk_sig + pr_sig + pk_prf.
        Ok(Self::new(compute_key.pk_sig() + compute_key.pr_sig() + pk_prf))
    }
}

#[cfg(feature = "view_key")]
impl<N: Network> TryFrom<ViewKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account view key.
    fn try_from(view_key: ViewKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&view_key)
    }
}

#[cfg(feature = "view_key")]
impl<N: Network> TryFrom<&ViewKey<N>> for Address<N> {
    type Error = Error;

    /// Derives the account address from an account view key.
    fn try_from(view_key: &ViewKey<N>) -> Result<Self, Self::Error> {
        // Compute G^view_key.
        Ok(Self::new(N::g_scalar_multiply(view_key)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1_000;

    #[test]
    fn test_try_from() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let expected = Address::try_from(private_key)?;

            // Check the address derived from the compute key.
            let compute_key = ComputeKey::<CurrentNetwork>::try_from(private_key)?;
            assert_eq!(expected, Address::try_from(compute_key)?);

            // Check the address derived from the view key.
            let view_key = ViewKey::<CurrentNetwork>::try_from(private_key)?;
            assert_eq!(expected, Address::try_from(view_key)?);
        }
        Ok(())
    }
}
