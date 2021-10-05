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

use crate::{
    traits::{AccountScheme, Network},
    Transaction,
};

use anyhow::Result;
use rand::{CryptoRng, Rng};

pub trait DPCScheme<N: Network>: Sized {
    type Account: AccountScheme;
    type LedgerProof;
    type StateTransition;

    /// Returns an authorization to execute a state transition.
    fn authorize<R: Rng + CryptoRng>(
        private_keys: &Vec<<Self::Account as AccountScheme>::PrivateKey>,
        transition: &Self::StateTransition,
        rng: &mut R,
    ) -> Result<Vec<N::AccountSignature>>;

    /// Returns a transaction by executing an authorized state transition.
    fn execute<R: Rng + CryptoRng>(
        signatures: Vec<N::AccountSignature>,
        transition: &Self::StateTransition,
        ledger_proof: Self::LedgerProof,
        rng: &mut R,
    ) -> Result<Transaction<N>>;
}
