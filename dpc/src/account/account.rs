// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{AccountError, AccountScheme, Address, Parameters, PrivateKey, ViewKey};

use rand::{CryptoRng, Rng};
use std::{convert::TryFrom, fmt};

#[derive(Derivative)]
#[derivative(Clone(bound = "C: Parameters"))]
pub struct Account<C: Parameters> {
    pub private_key: PrivateKey<C>,
    pub view_key: ViewKey<C>,
    pub address: Address<C>,
}

impl<C: Parameters> AccountScheme for Account<C> {
    type Address = Address<C>;
    type PrivateKey = PrivateKey<C>;
    type ViewKey = ViewKey<C>;

    /// Creates a new account.
    fn new<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, AccountError> {
        let private_key = PrivateKey::new(rng);
        let view_key = ViewKey::try_from(&private_key)?;
        let address = Address::try_from(&view_key)?;

        Ok(Self {
            private_key,
            view_key,
            address,
        })
    }
}

impl<C: Parameters> fmt::Display for Account<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Account {{ private_key: {}, view_key: {}, address: {} }}",
            self.private_key, self.view_key, self.address,
        )
    }
}

impl<C: Parameters> fmt::Debug for Account<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Account {{ private_key: {:?}, view_key: {:?}, address: {:?} }}",
            self.private_key, self.view_key, self.address,
        )
    }
}
