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
use snarkvm_experimental::{output, snark};
use snarkvm_fields::{PrimeField, Zero};
use snarkvm_utilities::{CryptoRng, Rng, ToBits, UniformRand};

use anyhow::{bail, Error, Result};
use core::panic::{RefUnwindSafe, UnwindSafe};
use rand::prelude::ThreadRng;
use snarkvm_algorithms::snark::marlin::Proof;
use snarkvm_curves::AffineCurve;
use std::{thread, time::Instant};

mod input {
    use circuit::{
        Aleo,
        Eject,
        Equal,
        Field,
        Group,
        Inject,
        Mode,
        Record,
        Scalar,
        SerialNumber,
        Signature,
        State,
        ToBits,
        U16,
    };

    use anyhow::{ensure, Result};

    pub struct Public<A: Aleo> {
        /// The input program root.
        root: Field<A>,
        /// The input serial number.
        serial_number: Field<A>,
        /// The address commitment (i.e. `acm := Commit(caller, randomizer)`).
        acm: Field<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the input circuit.
        pub fn from(root: A::BaseField, serial_number: A::BaseField, acm: A::BaseField) -> Self {
            let root = Field::<A>::new(Mode::Public, root);
            let serial_number = Field::<A>::new(Mode::Public, serial_number);
            let acm = Field::<A>::new(Mode::Public, acm);

            Self { root, serial_number, acm }
        }
    }

    pub struct Private<A: Aleo> {
        /// The input record view key.
        record_view_key: Field<A>,
        /// The input record.
        record: Record<A>,
        /// The input serial number proof.
        serial_number: SerialNumber<A>,
        /// The input signature.
        signature: Signature<A>,
        /// The address randomizer.
        r_acm: Scalar<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the input circuit.
        pub fn from(
            record_view_key: A::BaseField,
            record: console::program::Record<A::Network>,
            serial_number: console::program::SerialNumber<A::Network>,
            signature: console::account::Signature<A::Network>,
            r_acm: A::ScalarField,
        ) -> Self {
            let record_view_key = Field::<A>::new(Mode::Private, record_view_key);
            let record = Record::<A>::new(Mode::Private, record);
            let serial_number = SerialNumber::<A>::new(Mode::Private, serial_number);
            let signature = Signature::<A>::new(Mode::Private, signature);
            let r_acm = Scalar::<A>::new(Mode::Private, r_acm);

            Self { record_view_key, record, serial_number, signature, r_acm }
        }
    }

    pub struct InputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> InputCircuit<A> {
        /// Initializes the input circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { root, serial_number, acm } = &public;
            ensure!(root.eject_mode().is_public(), "Input root must be public");
            ensure!(serial_number.eject_mode().is_public(), "Input serial number must be public");
            ensure!(acm.eject_mode().is_public(), "Address commitment must be public");

            // Ensure all private members are private inputs.
            let Private { record_view_key, record, serial_number, signature, r_acm } = &private;
            ensure!(record_view_key.eject_mode().is_private(), "Input record view key must be private");
            ensure!(record.eject_mode().is_private(), "Input record must be private");
            ensure!(serial_number.eject_mode().is_private(), "Input serial number proof must be private");
            ensure!(signature.eject_mode().is_private(), "Input signature must be private");
            ensure!(r_acm.eject_mode().is_private(), "Address randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the input circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Decrypt the record into program state.
            let state = private.record.decrypt_symmetric(&private.record_view_key);
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the address commitment matches the record owner.
            A::assert_eq(&public.acm, A::commit_bhp256(&state.owner().to_bits_le(), &private.r_acm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Compute the record commitment.
            let commitment = private.record.to_commitment();
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the serial number is valid.
            A::assert(private.serial_number.verify(private.signature.compute_key().pk_vrf(), &commitment));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the serial number matches the declared serial number.
            A::assert_eq(&public.serial_number, private.serial_number.value());
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the signature is valid.
            A::assert(private.signature.verify(state.owner(), &[private.serial_number.value().clone()]));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // // Ensure the program state matches the declared state.
            // A::assert(state.is_equal(&private.state));
            // println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
        }
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
    /// The address commitment.
    acm: N::Field,
    fee: i64,
}

impl<N: Network> Transition<N> {
    /// Returns `true` if the transition is valid.
    pub fn verify(&self) -> bool {
        // self.
        true
    }

    /// Returns the commitments in the transition.
    pub fn to_commitments(&self) -> Result<Vec<N::Field>> {
        self.outputs.iter().map(|record| record.to_commitment()).collect::<Result<Vec<_>>>()
    }
}

fn acm<A: circuit::Aleo, R: Rng + CryptoRng>(
    caller: &Address<A::Network>,
    rng: &mut R,
) -> Result<(<A::Network as Network>::Field, <A::Network as Network>::Scalar)> {
    // TODO (howardwu): Domain separator.
    let randomizer = UniformRand::rand(rng);
    // TODO (howardwu): Add a to_bits impl for caller.
    let acm = A::Network::commit_bhp256(&(*caller).to_x_coordinate().to_bits_le(), &randomizer)?;
    Ok((acm, randomizer))
}

/// Transition: 0 -> 1
fn mint<A: circuit::Aleo, R: Rng + CryptoRng>(
    rng: &mut R,
    caller_view_key: &ViewKey<A::Network>,
) -> Result<Transaction<A::Network>>
where
    A::BaseField: UnwindSafe + RefUnwindSafe,
    A::ScalarField: UnwindSafe + RefUnwindSafe,
    A::Affine: UnwindSafe + RefUnwindSafe,
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

    fn bcm<A: circuit::Aleo>(
        b_in: u64,
        r_in: A::ScalarField,
        b_out: u64,
        r_out: A::ScalarField,
        fee: i64,
    ) -> Result<(A::BaseField, A::ScalarField)> {
        // TODO (howardwu): Enforce 2^52.
        let difference = b_in as i64 - b_out as i64 - fee;
        let r_bcm = r_in - r_out;
        // Compute bcm := G^(b_in - b_out - fee) H^(r_in - r_out).
        let bcm = A::Network::commit_ped64(&difference.abs().to_bits_le(), &r_bcm)?;
        // Ensure `bcm` == `G^0 H^(r_in - r_out)`.
        assert_eq!(bcm, A::Network::commit_ped64(&0u64.to_bits_le(), &r_bcm)?);
        Ok((bcm, r_bcm))
    }

    // Compute the record view key.
    let record_view_key = record.to_record_view_key(&caller_view_key);
    // Compute the randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
    let r_bcm = A::Network::hash_to_scalar_psd2(&[A::Network::bcm_domain(), record_view_key])?;

    let fee = -(state.balance() as i64);
    let (bcm, r_bcm) = bcm::<A>(0, A::ScalarField::zero(), state.balance(), r_bcm, fee)?;

    // Compute the address commitment.
    let (acm, r_acm) = acm::<A, R>(&caller_address, rng)?;

    let process = std::panic::catch_unwind(|| {
        // Set the output index to 0.
        let output_index = 0u16;
        // Compute the serial numbers digest.
        let serial_numbers_digest = A::Network::hash_bhp1024(&[])?;

        let public = output::Public::<A>::from(output_index, record.clone(), serial_numbers_digest, acm, bcm);
        let private = output::Private::<A>::from(state, randomizer, caller_address, r_acm, r_bcm);
        output::OutputCircuit::from(public, private)?.execute();
        println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

        let (num_constant, num_public, num_private, num_constraints, num_gates) = A::count();
        println!(
            "Count(Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, Gates: {num_gates})"
        );

        let timer = Instant::now();
        let assignment = circuit::Circuit::eject();
        println!("Convert to assignment: {} ms", timer.elapsed().as_millis());

        let proof = snark::execute(assignment)?;
        let transition = Transition {
            inputs: vec![],
            outputs: vec![record],
            input_proofs: vec![],
            output_proofs: vec![proof],
            acm,
            fee,
        };

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

    // Compute the record view key.
    let record_view_key = record.to_record_view_key(&caller_view_key);

    // Compute the serial number.
    let serial_number = record.to_serial_number(&caller_private_key, rng)?;
    // Compute the signature for the serial number.
    let signature = Signature::sign(&caller_private_key, &[*serial_number.value()], rng)?;

    // Compute the address commitment.
    let (acm, r_acm) = acm::<A, R>(&caller_address, rng)?;

    let process = std::panic::catch_unwind(|| {
        let public = input::Public::<A>::from(*root, *serial_number.value(), acm);
        let private = input::Private::<A>::from(record_view_key, record, serial_number.clone(), signature, r_acm);
        let input_circuit = input::InputCircuit::from(public, private)?;
        input_circuit.execute();

        let (num_constant, num_public, num_private, num_constraints, num_gates) = A::count();
        println!(
            "Count(Constant: {num_constant}, Public: {num_public}, Private: {num_private}, Constraints: {num_constraints}, Gates: {num_gates})"
        );

        let timer = Instant::now();
        let assignment = circuit::Circuit::eject();
        println!("Convert to assignment: {} ms", timer.elapsed().as_millis());

        let proof = snark::execute(assignment)?;
        let transition = Transition {
            inputs: vec![*serial_number.value()],
            outputs: vec![],
            input_proofs: vec![proof],
            output_proofs: vec![],
            acm,
            fee: 0i64,
        };

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
