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

pub mod compute_key;
pub use compute_key::*;

pub mod private_key;
pub use private_key::*;

pub mod signature;
pub use signature::*;

pub mod view_key;
pub use view_key::*;

#[cfg(test)]
mod helpers {
    use snarkvm_console_aleo::{
        Address as NativeAddress,
        ComputeKey as NativeComputeKey,
        PrivateKey as NativePrivateKey,
        Testnet3,
        ViewKey as NativeViewKey,
    };
    use snarkvm_utilities::test_crypto_rng;

    use anyhow::Result;

    type CurrentNetwork = Testnet3;

    #[allow(clippy::type_complexity)]
    pub(crate) fn generate_account() -> Result<(
        NativePrivateKey<CurrentNetwork>,
        NativeComputeKey<CurrentNetwork>,
        NativeViewKey<CurrentNetwork>,
        NativeAddress<CurrentNetwork>,
    )> {
        // Sample a random private key.
        let private_key = NativePrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;

        // Derive the compute key, view key, and address.
        let compute_key = NativeComputeKey::try_from(&private_key)?;
        let view_key = NativeViewKey::try_from(&private_key)?;
        let address = NativeAddress::try_from(&compute_key)?;

        // Return the private key and compute key components.
        Ok((private_key, compute_key, view_key, address))
    }
}
