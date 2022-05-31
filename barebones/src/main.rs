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

use console::{
    account::{Address, PrivateKey, Signature, ViewKey},
    collections::merkle_tree::MerkleTree,
    network::{Network, Testnet3},
    program::{Ciphertext, Data, Randomizer, Record, State},
};
use snarkvm_fields::Zero;
use snarkvm_utilities::UniformRand;

use anyhow::{bail, Result};
use std::thread;

mod output {
    use anyhow::{ensure, Result};
    use circuit::{Aleo, Eject, Equal, Field, Randomizer, Record, State, U16};

    struct Public<A: Aleo> {
        /// The output index.
        index: U16<A>,
        /// The output commitment.
        commitment: Field<A>,
        /// The output record.
        record: Record<A>,
        /// The serial numbers digest.
        serial_numbers_digest: Field<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the output circuit.
        pub fn new(
            index: U16<A>,
            commitment: Field<A>,
            record: Record<A>,
            serial_numbers_digest: Field<A>,
        ) -> Result<Self> {
            // Ensure all members are public inputs.
            ensure!(index.eject_mode().is_public(), "Output index must be public");
            ensure!(commitment.eject_mode().is_public(), "Output commitment must be public");
            ensure!(record.eject_mode().is_public(), "Output record must be public");
            ensure!(serial_numbers_digest.eject_mode().is_public(), "Serial numbers digest must be public");

            Ok(Self { index, commitment, record, serial_numbers_digest })
        }
    }

    struct Private<A: Aleo> {
        /// The output state.
        state: State<A>,
        /// The output randomizer.
        randomizer: Randomizer<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the output circuit.
        pub fn new(state: State<A>, randomizer: Randomizer<A>) -> Result<Self> {
            // Ensure all members are private inputs.
            ensure!(state.eject_mode().is_public(), "Output state must be private");
            ensure!(randomizer.eject_mode().is_public(), "Output randomizer must be private");

            Ok(Self { state, randomizer })
        }
    }

    pub struct OutputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> OutputCircuit<A> {
        /// Initializes the output circuit.
        pub fn new(
            index: U16<A>,
            commitment: Field<A>,
            record: Record<A>,
            serial_numbers_digest: Field<A>,
            state: State<A>,
            randomizer: Randomizer<A>,
        ) -> Result<Self> {
            Ok(Self(Public::new(index, commitment, record, serial_numbers_digest)?, Private::new(state, randomizer)?))
        }

        /// Executes the output circuit.
        pub fn execute(&self) -> Result<()> {
            let public = &self.0;
            let private = &self.1;

            // Ensure the randomizer is valid.
            A::assert(private.randomizer.verify(private.state.owner(), &public.serial_numbers_digest, &public.index));

            // Encrypt the program state into a new record.
            let record = private.state.encrypt(&private.randomizer);

            // Ensure the record matches the declared record.
            A::assert(record.is_equal(&public.record));

            // Ensure the record commitment matches the declared commitment.
            A::assert_eq(record.to_commitment(), &public.commitment);

            Ok(())
        }
    }
}

pub struct Transition<N: Network> {
    outputs: Vec<Record<N>>,
}

pub struct Transaction<N: Network> {
    network: u16,
    transitions: Vec<Transition<N>>,
}

impl<N: Network> Transition<N> {
    /// Returns the commitments in the transition.
    pub fn commitments(&self) -> Result<Vec<N::Field>> {
        self.outputs.iter().map(|record| record.to_commitment()).collect::<Result<Vec<_>>>()
    }
}

/// Transition: 0 -> 1
fn mint<A: circuit::Aleo>() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Initialize a new sender account.
    let sender_private_key = PrivateKey::<A::Network>::new(&mut rng)?;
    let sender_view_key = ViewKey::try_from(&sender_private_key)?;
    let sender_address = Address::try_from(&sender_private_key)?;

    // Initialize the randomizer, which is bound to the account of the **sender**.
    let randomizer = Randomizer::prove(&sender_view_key, &[], 0, &mut rng)?;

    // Initialize a coinbase.
    let (state, record) = {
        let program = <A::Network as Network>::Field::zero(); // TODO: Hardcode this option in the Network trait.
        let process = <A::Network as Network>::Field::zero(); // TODO: Hardcode this option in the Network trait.
        let owner = sender_address;
        let balance = 100u64;
        let data = <A::Network as Network>::Field::zero(); // TODO: Hardcode this option in the Network trait.

        let state = State::new(program, process, owner, balance, data, &randomizer);
        let record = state.encrypt(&randomizer)?;
        (state, record)
    };

    // let process = std::panic::catch_unwind(|| {
    {
        use circuit::{Field, Inject, Mode, Randomizer, Record, State, U16};

        // Set the output index to 0.
        let output_index = 0;
        // Compute the commitment.
        let commitment = record.to_commitment()?;
        // Compute the serial numbers digest.
        let serial_numbers_digest = A::Network::hash_bhp1024(&[])?;

        let index = U16::<A>::new(Mode::Public, output_index);
        let commitment = Field::<A>::new(Mode::Public, commitment);
        let record = Record::<A>::new(Mode::Public, record);
        let serial_numbers_digest = Field::<A>::new(Mode::Public, serial_numbers_digest);
        let state = State::<A>::new(Mode::Private, state);
        let randomizer = Randomizer::<A>::new(Mode::Private, randomizer);

        output::OutputCircuit::new(index, commitment, record, serial_numbers_digest, state, randomizer)?;
    }

    //     Ok(0)
    // });
    //
    // match process {
    //     Ok(Ok(result)) => println!("{}", result),
    //     Err(_) => println!("Error"),
    // }

    // let serial_number = state.to_serial_number(&sender_private_key, &mut rng)?;

    // Signature::sign(&sender_private_key, &[]);

    // let transition = Transition { outputs: vec![record] };
    //
    // let transaction = Transaction { network: 0, transitions: vec![transition] };

    println!("Success");
    Ok(())
}

// /// Transition: 1 -> 1
// fn run<N: Network>() -> Result<()> {
//     let mut rng = rand::thread_rng();
//
//     // Initialize a prior account.
//     let prior_private_key = PrivateKey::new(&mut rng)?;
//     let prior_view_key = ViewKey::try_from(&prior_private_key)?;
//
//     // Initialize a new sender account.
//     let sender_private_key = PrivateKey::new(&mut rng)?;
//     let sender_view_key = ViewKey::try_from(&sender_private_key)?;
//     let sender_address = Address::try_from(&sender_private_key)?;
//
//     // Initialize a coinbase.
//     let (state, record) = {
//         let program = N::Field::rand(&mut rng);
//         let process = N::Field::rand(&mut rng);
//         let owner = sender_address;
//         let balance = 100u64;
//         let data = Data::<N, Ciphertext<N>>::from(vec![]);
//         let nonce = N::Affine::rand(&mut rng);
//
//         let state = State::new(program, process, owner, balance, data, nonce);
//
//
//         // Compute the encryption randomizer, which is bound to the account of the **sender**.
//         let randomizer = Randomizer::prove(prior_view_key, serial_numbers, output_index, rng)?;
//
//         let record = state.encrypt(&prior_view_key, &[], 0, &mut rng)?;
//
//         (state, record)
//     };
//
//     // Initialize a program tree with the coinbase record.
//     // let program = N::merkle_tree_bhp(&[record.to_bits_le()])?; // TODO: Add test that record ID matches in tree.
//
//     let commitment = state.to_commitment()?;
//     let serial_number = state.to_serial_number(&sender_private_key, &mut rng)?;
//
//     // Signature::sign(&sender_private_key, &[*serial_number.value()], )
//
//     // Initialize a new receiver address.
//     let receiver_private_key = PrivateKey::new(&mut rng)?;
//     let receiver_view_key = ViewKey::try_from(&receiver_private_key)?;
//     let receiver_address = Address::try_from(&receiver_private_key)?;
//
//     // Initialize an instance of program state.
//     let (state, commitment) = {
//         let program = N::Field::rand(&mut rng);
//         let process = N::Field::rand(&mut rng);
//         let owner = receiver_address;
//         let balance = 100u64;
//         let data = Data::<N, Ciphertext<N>>::from(vec![]);
//         let nonce = N::Affine::rand(&mut rng);
//
//         let state = State::new(program, process, owner, balance, data, nonce);
//         let commitment = state.to_commitment()?;
//
//         (state, commitment)
//     };
//
//     // Derive the record corresponding to the program state.
//     let serial_number = state.to_serial_number(&sender_private_key, &mut rng)?;
//     let record = state.encrypt(&sender_view_key, &[*serial_number.value()], 0, &mut rng)?;
//
//     Ok(())
// }

fn main() -> Result<()> {
    mint::<circuit::AleoV0>()?;

    Ok(())
}
