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

use crate::errors::AccountError;

use rand::{CryptoRng, Rng};

pub trait AccountScheme: Sized {
    type Address: Copy + Clone + Default;
    type PrivateKey;
    type ViewKey;

    /// Creates a new account.
    fn new<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, AccountError>;

    /// Returns a reference to the private key.
    fn private_key(&self) -> &Self::PrivateKey;

    /// Returns a reference to the address.
    fn address(&self) -> Self::Address;
}
