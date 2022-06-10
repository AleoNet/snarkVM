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

static ACCOUNT_SK_SIG_DOMAIN: &str = "AleoAccountSignatureSecretKey0";
static ACCOUNT_R_SIG_DOMAIN: &str = "AleoAccountSignatureRandomizer0";

impl<N: Network> PrivateKey<N> {
    /// Returns the account private key from an account seed.
    #[inline]
    pub fn try_from(seed: Scalar<N>) -> Result<Self> {
        // Construct the sk_sig domain separator.
        let sk_sig_domain = N::Scalar::from_bytes_le_mod_order(ACCOUNT_SK_SIG_DOMAIN.as_bytes());

        // Construct the r_sig domain separator.
        let r_sig_input = format!("{}.{}", ACCOUNT_R_SIG_DOMAIN, 0);
        let r_sig_domain = N::Scalar::from_bytes_le_mod_order(r_sig_input.as_bytes());

        Ok(Self {
            seed,
            sk_sig: Scalar::new(N::prf_psd2s(&seed, &[sk_sig_domain])?),
            r_sig: Scalar::new(N::prf_psd2s(&seed, &[r_sig_domain])?),
        })
    }
}
