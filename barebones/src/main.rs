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

use circuit;
use console::{
    account::{Address, PrivateKey, Signature, ViewKey},
    collections::merkle_tree::MerkleTree,
    network::{Network, Testnet3},
    program::{Ciphertext, Data, Record, State},
};

use snarkvm_utilities::UniformRand;

use anyhow::Result;

fn run<N: Network>() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Initialize a prior account.
    let prior_private_key = PrivateKey::new(&mut rng)?;
    let prior_view_key = ViewKey::try_from(&prior_private_key)?;

    // Initialize a new sender account.
    let sender_private_key = PrivateKey::new(&mut rng)?;
    let sender_view_key = ViewKey::try_from(&sender_private_key)?;
    let sender_address = Address::try_from(&sender_private_key)?;

    // Initialize a coinbase.
    let (state, record) = {
        let program = N::Field::rand(&mut rng);
        let process = N::Field::rand(&mut rng);
        let owner = sender_address;
        let balance = 100u64;
        let data = Data::<N, Ciphertext<N>>::from(vec![]);
        let nonce = N::Affine::rand(&mut rng);

        let state = State::new(program, process, owner, balance, data, nonce);
        let record = state.encrypt(&prior_view_key, &[], 0, &mut rng)?;

        (state, record)
    };

    // Initialize a program tree with the coinbase record.
    // let program = N::merkle_tree_bhp(&[record.to_bits_le()])?; // TODO: Add test that record ID matches in tree.

    let commitment = state.to_commitment()?;
    let serial_number = state.to_serial_number(&sender_private_key, &mut rng)?;

    // Signature::sign(&sender_private_key, serial_number)

    // Initialize a new receiver address.
    let receiver_private_key = PrivateKey::new(&mut rng)?;
    let receiver_view_key = ViewKey::try_from(&receiver_private_key)?;
    let receiver_address = Address::try_from(&receiver_private_key)?;

    // Initialize an instance of program state.
    let (state, commitment) = {
        let program = N::Field::rand(&mut rng);
        let process = N::Field::rand(&mut rng);
        let owner = receiver_address;
        let balance = 100u64;
        let data = Data::<N, Ciphertext<N>>::from(vec![]);
        let nonce = N::Affine::rand(&mut rng);

        let state = State::new(program, process, owner, balance, data, nonce);
        let commitment = state.to_commitment()?;

        (state, commitment)
    };

    // Derive the record corresponding to the program state.
    let serial_number = state.to_serial_number(&sender_private_key, &mut rng)?;
    let record = state.encrypt(&sender_view_key, &[*serial_number.value()], 0, &mut rng)?;

    Ok(())
}

fn main() -> Result<()> {
    run::<Testnet3>()?;

    Ok(())
}
