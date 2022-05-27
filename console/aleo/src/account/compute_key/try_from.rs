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

impl<N: Network> TryFrom<PrivateKey<N>> for ComputeKey<N> {
    type Error = Error;

    /// Derives the account compute key from an account private key.
    fn try_from(private_key: PrivateKey<N>) -> Result<Self, Self::Error> {
        Self::try_from(&private_key)
    }
}

impl<N: Network> TryFrom<&PrivateKey<N>> for ComputeKey<N> {
    type Error = Error;

    /// Derives the account compute key from an account private key.
    fn try_from(private_key: &PrivateKey<N>) -> Result<Self, Self::Error> {
        // Compute pk_sig := G^sk_sig.
        let pk_sig = N::g_scalar_multiply(&private_key.sk_sig());
        // Compute pr_sig := G^r_sig.
        let pr_sig = N::g_scalar_multiply(&private_key.r_sig());
        // Compute pk_vrf := G^sk_vrf.
        let pk_vrf = N::g_scalar_multiply(&private_key.sk_vrf());

        // Convert (pk_sig, pr_sig, pk_vrf) into affine coordinates.
        let (pk_sig, pr_sig, pk_vrf) = {
            let mut to_normalize = [pk_sig, pr_sig, pk_vrf];
            <N::Affine as AffineCurve>::Projective::batch_normalization(&mut to_normalize);
            let [pk_sig, pr_sig, pk_vrf] = to_normalize.map(|c| c.to_affine());
            (pk_sig, pr_sig, pk_vrf)
        };

        // Output the compute key.
        Self::try_from((pk_sig, pr_sig, pk_vrf))
    }
}

impl<N: Network> TryFrom<(N::Affine, N::Affine, N::Affine)> for ComputeKey<N> {
    type Error = Error;

    /// Derives the account compute key from a tuple `(pk_sig, pr_sig, pk_vrf)`.
    fn try_from((pk_sig, pr_sig, pk_vrf): (N::Affine, N::Affine, N::Affine)) -> Result<Self> {
        Self::try_from(&(pk_sig, pr_sig, pk_vrf))
    }
}

impl<N: Network> TryFrom<&(N::Affine, N::Affine, N::Affine)> for ComputeKey<N> {
    type Error = Error;

    /// Derives the account compute key from a tuple `(pk_sig, pr_sig, pk_vrf)`.
    fn try_from((pk_sig, pr_sig, pk_vrf): &(N::Affine, N::Affine, N::Affine)) -> Result<Self> {
        // Compute sk_prf := HashToScalar(pk_sig || pr_sig || pk_vrf).
        let sk_prf =
            N::hash_to_scalar_psd4(&[pk_sig.to_x_coordinate(), pr_sig.to_x_coordinate(), pk_vrf.to_x_coordinate()])?;
        // Output the compute key.
        Ok(Self { pk_sig: *pk_sig, pr_sig: *pr_sig, pk_vrf: *pk_vrf, sk_prf })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::Testnet3;
    use snarkvm_utilities::test_crypto_rng;

    use anyhow::Result;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1000;

    #[test]
    fn test_try_from() -> Result<()> {
        for _ in 0..ITERATIONS {
            // Sample a new compute key.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let candidate = ComputeKey::try_from(private_key)?;

            // Check that sk_prf matches.
            // Compute sk_prf := HashToScalar(pk_sig || pr_sig || pk_vrf).
            let candidate_sk_prf = CurrentNetwork::hash_to_scalar_psd4(&[
                candidate.pk_sig().to_x_coordinate(),
                candidate.pr_sig().to_x_coordinate(),
                candidate.pk_vrf().to_x_coordinate(),
            ])?;
            assert_eq!(candidate.sk_prf(), candidate_sk_prf);

            // Check that compute key is derived correctly from the tuple `(pk_sig, pr_sig, pk_vrf)`.
            assert_eq!(candidate, ComputeKey::try_from((candidate.pk_sig(), candidate.pr_sig(), candidate.pk_vrf()))?);
        }
        Ok(())
    }
}
