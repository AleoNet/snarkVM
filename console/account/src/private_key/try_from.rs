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
use snarkvm_console_types::Field;

static ACCOUNT_SK_SIG_DOMAIN: &str = "AleoAccountSignatureSecretKey0";
static ACCOUNT_R_SIG_DOMAIN: &str = "AleoAccountSignatureRandomizer0";

impl<N: Network> PrivateKey<N> {
    /// Returns the account private key from an account seed.
    #[inline]
    pub fn try_from(seed: Field<N>) -> Result<Self> {
        // Construct the sk_sig domain separator.
        let sk_sig_domain = Field::<N>::new_domain_separator(ACCOUNT_SK_SIG_DOMAIN);

        // Construct the r_sig domain separator.
        let r_sig_input = format!("{}.{}", ACCOUNT_R_SIG_DOMAIN, 0);
        let r_sig_domain = Field::new_domain_separator(&r_sig_input);

        Ok(Self {
            seed,
            sk_sig: N::hash_to_scalar_psd2(&[sk_sig_domain, seed])?,
            r_sig: N::hash_to_scalar_psd2(&[r_sig_domain, seed])?,
        })
    }
}
