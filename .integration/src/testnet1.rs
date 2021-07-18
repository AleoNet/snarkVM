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

use crate::Ledger;
use snarkvm_dpc::{testnet1::gm17::*, Account, AccountScheme, DPCComponents, DPCScheme, Storage};

use rand::{CryptoRng, Rng};
use std::sync::Arc;

pub type MerkleTreeLedger<S> = Ledger<Testnet1Transaction, CommitmentMerkleTreeParameters, S>;

pub fn setup_or_load_parameters<R: Rng + CryptoRng, S: Storage>(
    verify_only: bool,
    rng: &mut R,
) -> (Arc<CommitmentMerkleTreeParameters>, Testnet1DPC) {
    // TODO (howardwu): TEMPORARY - Resolve this inconsistency on import structure with a new model once MerkleParameters are refactored.
    let ledger_merkle_tree_parameters = Arc::new(Components::ledger_merkle_tree_parameters().clone());

    let dpc = match <Testnet1DPC as DPCScheme<MerkleTreeLedger<S>>>::load(verify_only) {
        Ok(dpc) => dpc,
        Err(err) => {
            println!("error - {}, re-running parameter Setup", err);
            <Testnet1DPC as DPCScheme<MerkleTreeLedger<S>>>::setup(&ledger_merkle_tree_parameters, rng)
                .expect("DPC setup failed")
        }
    };

    (ledger_merkle_tree_parameters, dpc)
}

pub fn generate_test_accounts<R: Rng + CryptoRng>(rng: &mut R) -> [Account<Components>; 3] {
    let genesis_account = Account::new(rng).unwrap();
    let account_1 = Account::new(rng).unwrap();
    let account_2 = Account::new(rng).unwrap();

    [genesis_account, account_1, account_2]
}
