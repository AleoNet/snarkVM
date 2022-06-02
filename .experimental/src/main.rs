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
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_utilities::{CryptoRng, Rng, ToBits, UniformRand};

use anyhow::{bail, Error, Result};
use core::panic::{RefUnwindSafe, UnwindSafe};
use rand::prelude::ThreadRng;
use snarkvm_algorithms::snark::marlin::Proof;
use std::{thread, time::Instant};

mod output {
    use circuit::{Aleo, Eject, Equal, Field, Inject, Mode, Randomizer, Record, State, U16};

    use anyhow::{ensure, Result};

    pub struct Public<A: Aleo> {
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
        pub fn from(
            index: u16,
            commitment: A::BaseField,
            record: console::program::Record<A::Network>,
            serial_numbers_digest: A::BaseField,
        ) -> Self {
            let index = U16::<A>::new(Mode::Public, index);
            let commitment = Field::<A>::new(Mode::Public, commitment);
            let record = Record::<A>::new(Mode::Public, record);
            let serial_numbers_digest = Field::<A>::new(Mode::Public, serial_numbers_digest);

            Self { index, commitment, record, serial_numbers_digest }
        }
    }

    pub struct Private<A: Aleo> {
        /// The output state.
        state: State<A>,
        /// The output randomizer.
        randomizer: Randomizer<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the output circuit.
        pub fn from(
            state: console::program::State<A::Network>,
            randomizer: console::program::Randomizer<A::Network>,
        ) -> Self {
            let state = State::<A>::new(Mode::Private, state);
            let randomizer = Randomizer::<A>::new(Mode::Private, randomizer);

            Self { state, randomizer }
        }
    }

    pub struct OutputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> OutputCircuit<A> {
        /// Initializes the output circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            ensure!(public.index.eject_mode().is_public(), "Output index must be public");
            ensure!(public.commitment.eject_mode().is_public(), "Output commitment must be public");
            ensure!(public.record.eject_mode().is_public(), "Output record must be public");
            ensure!(public.serial_numbers_digest.eject_mode().is_public(), "Serial numbers digest must be public");

            // Ensure all private members are private inputs.
            ensure!(private.state.eject_mode().is_private(), "Output state must be private");
            ensure!(private.randomizer.eject_mode().is_private(), "Output randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the output circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Ensure the randomizer is valid.
            A::assert(private.randomizer.verify(private.state.owner(), &public.serial_numbers_digest, &public.index));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Encrypt the program state into a new record.
            let record = private.state.encrypt(&private.randomizer);
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the record matches the declared record.
            A::assert(record.is_equal(&public.record));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the record commitment matches the declared commitment.
            A::assert_eq(record.to_commitment(), &public.commitment);
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            let (num_constant, num_public, num_private, num_constraints, num_gates) = A::count();
            println!(
                "Count(Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, Gates: {num_gates})"
            );
        }
    }
}

mod snark {
    use snarkvm_algorithms::{
        crypto_hash::PoseidonSponge,
        snark::marlin::{
            ahp::AHPForR1CS,
            fiat_shamir::FiatShamirAlgebraicSpongeRng,
            MarlinHidingMode,
            MarlinSNARK,
            Proof,
        },
        SNARK,
    };
    use snarkvm_curves::bls12_377::Bls12_377;
    use snarkvm_fields::One;

    use anyhow::{ensure, Result};
    use std::time::Instant;

    type EC = snarkvm_curves::bls12_377::Bls12_377;
    type Fq = <EC as snarkvm_curves::PairingEngine>::Fq;
    type Fr = <EC as snarkvm_curves::PairingEngine>::Fr;
    type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
    type Marlin = MarlinSNARK<EC, FS, MarlinHidingMode, [Fr]>;

    // Runs Marlin setup, prove, and verify.
    pub fn execute(assignment: circuit::Assignment<Fr>) -> Result<Proof<Bls12_377>> {
        let mut rng = rand::thread_rng();

        let timer = Instant::now();
        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(100000, 100000, 100000).unwrap();
        let universal_srs = Marlin::universal_setup(&max_degree, &mut rng).unwrap();
        println!("Called universal setup: {} ms", timer.elapsed().as_millis());

        ensure!(<circuit::Circuit as circuit::Environment>::is_satisfied(), "Circuit is not satisfied");

        let timer = Instant::now();
        let (index_pk, index_vk) = Marlin::circuit_setup(&universal_srs, &assignment).unwrap();
        println!("Called setup: {} ms", timer.elapsed().as_millis());

        let timer = Instant::now();
        let proof = Marlin::prove_batch(&index_pk, std::slice::from_ref(&assignment), &mut rng).unwrap();
        println!("Called prover: {} ms", timer.elapsed().as_millis());

        let inputs = assignment.public_inputs();
        println!("{} inputs: {:?}", inputs.len(), inputs);

        let timer = Instant::now();
        assert!(Marlin::verify(&index_vk, inputs, &proof).unwrap());
        println!("Called verifier: {} ms", timer.elapsed().as_millis());

        // Ok((inputs, proof))
        Ok(proof)
    }
}

pub struct Transaction<N: Network> {
    network: u16,
    transitions: Vec<Transition<N>>,
}

impl<N: Network> Transaction<N> {
    /// Returns the transitions in the transaction.
    pub fn transitions(&self) -> &Vec<Transition<N>> {
        &self.transitions
    }
}

pub struct Transition<N: Network> {
    inputs: Vec<N::Field>,
    outputs: Vec<Record<N>>,
    input_proofs: Vec<Proof<snarkvm_curves::bls12_377::Bls12_377>>,
    output_proofs: Vec<Proof<snarkvm_curves::bls12_377::Bls12_377>>,
}

impl<N: Network> Transition<N> {
    /// Returns the commitments in the transition.
    pub fn to_commitments(&self) -> Result<Vec<N::Field>> {
        self.outputs.iter().map(|record| record.to_commitment()).collect::<Result<Vec<_>>>()
    }
}

/// Transition: 0 -> 1
fn mint<A: circuit::Aleo, R: Rng + CryptoRng>(
    rng: &mut R,
    caller_view_key: &ViewKey<A::Network>,
) -> Result<Transaction<A::Network>>
where
    A::BaseField: UnwindSafe,
    A::ScalarField: UnwindSafe,
    A::Affine: UnwindSafe,
{
    // Initialize the caller address.
    let caller_address = Address::try_from(caller_view_key)?;

    // Initialize the randomizer, which is bound to the account of the **sender**.
    let randomizer = Randomizer::prove(&caller_view_key, &[], 0, rng)?;

    // Initialize a coinbase.
    let (state, record) = {
        let program = <A::Network as Network>::Field::zero(); // TODO: Hardcode this option in the Network trait.
        let process = <A::Network as Network>::Field::zero(); // TODO: Hardcode this option in the Network trait.
        let owner = caller_address;
        let balance = 100u64;
        let data = <A::Network as Network>::Field::zero(); // TODO: Hardcode this option in the Network trait.

        let state = State::new(program, process, owner, balance, data, &randomizer);
        let record = state.encrypt(&randomizer)?;
        (state, record)
    };

    let process = std::panic::catch_unwind(|| {
        // Set the output index to 0.
        let output_index = 0u16;
        // Compute the commitment.
        let commitment = record.to_commitment()?;
        // Compute the serial numbers digest.
        let serial_numbers_digest = A::Network::hash_bhp1024(&[])?;

        let public = output::Public::<A>::from(output_index, commitment, record.clone(), serial_numbers_digest);
        let private = output::Private::<A>::from(state, randomizer);
        let output_circuit = output::OutputCircuit::from(public, private)?;
        output_circuit.execute();

        let timer = Instant::now();
        let assignment = circuit::Circuit::eject();
        println!("Convert to assignment: {} ms", timer.elapsed().as_millis());

        let proof = snark::execute(assignment)?;
        let transition =
            Transition { inputs: vec![], outputs: vec![record], input_proofs: vec![], output_proofs: vec![proof] };

        // Set the network ID to 0.
        let network = 0u16;
        let transaction = Transaction { network, transitions: vec![transition] };

        Ok::<_, Error>(transaction)
    });

    match process {
        Ok(Ok(transaction)) => Ok(transaction),
        Ok(Err(error)) => bail!("{:?}", error),
        Err(_) => bail!("Thread failed"),
    }
}

/// Transition: 1 -> 0
fn burn<A: circuit::Aleo, R: Rng + CryptoRng>(rng: &mut R) -> Result<Transaction<A::Network>>
where
    A::BaseField: UnwindSafe + RefUnwindSafe,
    A::ScalarField: UnwindSafe + RefUnwindSafe,
    A::Affine: UnwindSafe + RefUnwindSafe,
{
    // Initialize a new caller account.
    let caller_private_key = PrivateKey::<A::Network>::new(rng)?;
    let caller_view_key = ViewKey::try_from(&caller_private_key)?;
    let caller_address = Address::try_from(&caller_private_key)?;

    // Generate a prior coinbase transaction.
    let transaction = mint::<A, R>(rng, &caller_view_key)?;

    // Retrieve the coinbase record.
    let record = transaction.transitions()[0].outputs[0].clone();

    // Initialize a program tree with the coinbase record.
    let program = A::Network::merkle_tree_bhp::<32>(&[record.to_bits_le()])?; // TODO: Add test that record ID matches in tree.
    // Compute a Merkle path for the coinbase record.
    let path = program.prove(0, &record.to_bits_le())?;
    // Retrieve the Merkle root.
    let root = program.root();

    // Decrypt the record into state.
    let state = record.decrypt(&caller_view_key)?;

    // Compute the serial number.
    let serial_number = state.to_serial_number(&caller_private_key, rng)?;

    // Compute the commitment.
    let commitment = record.to_commitment()?;

    // Compute the signature for the serial number.
    let signature = Signature::sign(&caller_private_key, &[commitment], rng)?;

    // Compute the record view key.
    let record_view_key = record.to_record_view_key(&caller_view_key);

    let process = std::panic::catch_unwind(|| {
        // Set the input index to 0.
        let input_index = 0u16;

        let public = input::Public::<A>::from(input_index, *root, *serial_number.value());
        let private = input::Private::<A>::from(record_view_key, record, state, serial_number.clone(), signature);
        let input_circuit = input::InputCircuit::from(public, private)?;
        input_circuit.execute();

        let timer = Instant::now();
        let assignment = circuit::Circuit::eject();
        println!("Convert to assignment: {} ms", timer.elapsed().as_millis());

        let proof = snark::execute(assignment)?;
        let transition = Transition {
            inputs: vec![*serial_number.value()],
            outputs: vec![],
            input_proofs: vec![proof],
            output_proofs: vec![],
        };

        // Set the network ID to 0.
        let network = 0u16;
        let transaction = Transaction { network, transitions: vec![transition] };

        Ok::<_, Error>(transaction)
    });

    mod input {
        use circuit::{
            Aleo,
            Eject,
            Equal,
            Field,
            Inject,
            Mode,
            Randomizer,
            Record,
            SerialNumber,
            Signature,
            State,
            U16,
        };

        use anyhow::{ensure, Result};

        pub struct Public<A: Aleo> {
            /// The input index.
            index: U16<A>,
            /// The input program root.
            root: Field<A>,
            /// The input serial number.
            serial_number: Field<A>,
        }

        impl<A: Aleo> Public<A> {
            /// Initializes the public inputs for the input circuit.
            pub fn from(index: u16, root: A::BaseField, serial_number: A::BaseField) -> Self {
                let index = U16::<A>::new(Mode::Public, index);
                let root = Field::<A>::new(Mode::Public, root);
                let serial_number = Field::<A>::new(Mode::Public, serial_number);

                Self { index, root, serial_number }
            }
        }

        pub struct Private<A: Aleo> {
            /// The input record view key.
            record_view_key: Field<A>,
            /// The input record.
            record: Record<A>,
            /// The input state.
            state: State<A>,
            /// The input serial number proof.
            serial_number: SerialNumber<A>,
            /// The input signature.
            signature: Signature<A>,
        }

        impl<A: Aleo> Private<A> {
            /// Initializes the private inputs for the input circuit.
            pub fn from(
                record_view_key: A::BaseField,
                record: console::program::Record<A::Network>,
                state: console::program::State<A::Network>,
                serial_number: console::program::SerialNumber<A::Network>,
                signature: console::account::Signature<A::Network>,
            ) -> Self {
                let record_view_key = Field::<A>::new(Mode::Private, record_view_key);
                let record = Record::<A>::new(Mode::Private, record);
                let state = State::<A>::new(Mode::Private, state);
                let serial_number = SerialNumber::<A>::new(Mode::Private, serial_number);
                let signature = Signature::<A>::new(Mode::Private, signature);

                Self { record_view_key, record, state, serial_number, signature }
            }
        }

        pub struct InputCircuit<A: Aleo>(Public<A>, Private<A>);

        impl<A: Aleo> InputCircuit<A> {
            /// Initializes the input circuit.
            pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
                // Ensure all public members are public inputs.
                ensure!(public.index.eject_mode().is_public(), "Input index must be public");
                ensure!(public.root.eject_mode().is_public(), "Input program root must be public");
                ensure!(public.serial_number.eject_mode().is_public(), "Input serial number must be public");

                // Ensure all private members are private inputs.
                ensure!(private.record_view_key.eject_mode().is_private(), "Input record view key must be private");
                ensure!(private.record.eject_mode().is_private(), "Input record must be private");
                ensure!(private.state.eject_mode().is_private(), "Input state must be private");
                ensure!(private.serial_number.eject_mode().is_private(), "Input serial number proof must be private");
                ensure!(private.signature.eject_mode().is_private(), "Input signature must be private");

                Ok(Self(public, private))
            }

            /// Executes the input circuit.
            pub fn execute(&self) {
                let (public, private) = (&self.0, &self.1);

                // Compute the record commitment.
                let commitment = private.record.to_commitment();
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Decrypt the record into program state.
                let state = private.record.decrypt_symmetric(&private.record_view_key);
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // // Ensure the program state matches the declared state.
                // A::assert(state.is_equal(&private.state));
                // println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                let (num_constant, num_public, num_private, num_constraints, num_gates) = A::count();
                println!(
                    "Count(Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, Gates: {num_gates})"
                );
            }
        }
    }

    match process {
        Ok(Ok(transaction)) => Ok(transaction),
        Ok(Err(error)) => bail!("{:?}", error),
        Err(_) => bail!("Thread failed"),
    }
}

fn main() -> Result<()> {
    let mut rng = rand::thread_rng();

    // // Initialize a new caller account.
    // let caller_private_key = PrivateKey::<<circuit::AleoV0 as circuit::Environment>::Network>::new(&mut rng)?;
    // let caller_view_key = ViewKey::try_from(&caller_private_key)?;
    // let caller_address = Address::try_from(&caller_private_key)?;
    //
    // let transaction = mint::<circuit::AleoV0, ThreadRng>(&mut rng, &caller_view_key)?;

    let transaction = burn::<circuit::AleoV0, ThreadRng>(&mut rng)?;

    Ok(())
}
