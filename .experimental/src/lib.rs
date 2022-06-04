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

#![forbid(unsafe_code)]

pub mod input {
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
        Zero,
        U16,
        U64,
    };

    use anyhow::{ensure, Result};

    pub struct Public<A: Aleo> {
        /// The input program root.
        root: Field<A>,
        /// The input serial number.
        serial_number: Field<A>,
        /// The address commitment (i.e. `acm := Commit(caller, r_acm)`).
        acm: Field<A>,
        /// The re-randomized balance commitment (i.e. `bcm := Commit(balance, r_bcm + r_bcm')`).
        bcm: Group<A>,
        /// The fee commitment (i.e. `fcm := Σ bcm_in - Σ bcm_out - Commit(fee, 0) = Commit(0, r_fcm)`).
        fcm: Group<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the input circuit.
        pub fn from(
            root: A::BaseField,
            serial_number: A::BaseField,
            acm: A::BaseField,
            bcm: A::Affine,
            fcm: A::Affine,
        ) -> Self {
            Self {
                root: Field::<A>::new(Mode::Public, root),
                serial_number: Field::<A>::new(Mode::Public, serial_number),
                acm: Field::<A>::new(Mode::Public, acm),
                bcm: Group::<A>::new(Mode::Public, bcm),
                fcm: Group::<A>::new(Mode::Public, fcm),
            }
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
        /// The fee randomizer (i.e. `r_fcm := Σ r_in - Σ r_out`).
        r_fcm: Scalar<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the input circuit.
        pub fn from(
            record_view_key: A::BaseField,
            record: console::program::Record<A::Network>,
            serial_number: console::program::SerialNumber<A::Network>,
            signature: console::account::Signature<A::Network>,
            r_acm: A::ScalarField,
            r_fcm: A::ScalarField,
        ) -> Self {
            Self {
                record_view_key: Field::<A>::new(Mode::Private, record_view_key),
                record: Record::<A>::new(Mode::Private, record),
                serial_number: SerialNumber::<A>::new(Mode::Private, serial_number),
                signature: Signature::<A>::new(Mode::Private, signature),
                r_acm: Scalar::<A>::new(Mode::Private, r_acm),
                r_fcm: Scalar::<A>::new(Mode::Private, r_fcm),
            }
        }
    }

    pub struct InputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> InputCircuit<A> {
        /// Initializes the input circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { root, serial_number, acm, bcm, fcm } = &public;
            ensure!(root.eject_mode().is_public(), "Input root must be public");
            ensure!(serial_number.eject_mode().is_public(), "Input serial number must be public");
            ensure!(acm.eject_mode().is_public(), "Address commitment must be public");
            ensure!(bcm.eject_mode().is_public(), "Balance commitment must be public");
            ensure!(fcm.eject_mode().is_public(), "Fee commitment must be public");

            // Ensure all private members are private inputs.
            let Private { record_view_key, record, serial_number, signature, r_acm, r_fcm } = &private;
            ensure!(record_view_key.eject_mode().is_private(), "Input record view key must be private");
            ensure!(record.eject_mode().is_private(), "Input record must be private");
            ensure!(serial_number.eject_mode().is_private(), "Input serial number proof must be private");
            ensure!(signature.eject_mode().is_private(), "Input signature must be private");
            ensure!(r_acm.eject_mode().is_private(), "Address randomizer must be private");
            ensure!(r_fcm.eject_mode().is_private(), "Fee randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the input circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Decrypt the record into program state.
            let state = private.record.decrypt_symmetric(&private.record_view_key);
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the address commitment matches the state owner.
            A::assert_eq(&public.acm, A::commit_bhp256(&state.owner().to_bits_le(), &private.r_acm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Compute the re-randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
            let r_bcm = A::hash_to_scalar_psd2(&[A::r_bcm_domain(), private.record_view_key.clone()]);
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the randomized balance commitment is based on the original balance commitment.
            A::assert_eq(&public.bcm, private.record.bcm() + &A::commit_ped64(&U64::zero().to_bits_le(), &r_bcm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the fee commitment is correct.
            A::assert_eq(&public.fcm, A::commit_ped64(&U64::zero().to_bits_le(), &private.r_fcm));
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
        }
    }
}

pub mod output {
    use circuit::{
        Address,
        Aleo,
        Eject,
        Equal,
        Field,
        Group,
        Inject,
        Mode,
        Randomizer,
        Record,
        Scalar,
        State,
        ToBits,
        Zero,
        U16,
        U64,
    };

    use anyhow::{ensure, Result};

    pub struct Public<A: Aleo> {
        /// The output index.
        index: U16<A>,
        /// The output record.
        record: Record<A>,
        /// The serial numbers digest.
        serial_numbers_digest: Field<A>,
        /// The address commitment (i.e. `acm := Commit(caller, r_acm)`).
        acm: Field<A>,
        /// The fee commitment (i.e. `fcm := Σ bcm_in - Σ bcm_out - Commit(fee, 0) = Commit(0, r_fcm)`).
        fcm: Group<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the output circuit.
        pub fn from(
            index: u16,
            record: console::program::Record<A::Network>,
            serial_numbers_digest: A::BaseField,
            acm: A::BaseField,
            fcm: A::Affine,
        ) -> Self {
            let index = U16::<A>::new(Mode::Public, index);
            let record = Record::<A>::new(Mode::Public, record);
            let serial_numbers_digest = Field::<A>::new(Mode::Public, serial_numbers_digest);
            let acm = Field::<A>::new(Mode::Public, acm);
            let fcm = Group::<A>::new(Mode::Public, fcm);

            Self { index, record, serial_numbers_digest, acm, fcm }
        }
    }

    pub struct Private<A: Aleo> {
        /// The output state.
        state: State<A>,
        /// The output randomizer.
        randomizer: Randomizer<A>,
        /// The caller address.
        caller: Address<A>,
        /// The address randomizer.
        r_acm: Scalar<A>,
        /// The fee randomizer (i.e. `r_fcm := Σ r_in - Σ r_out`).
        r_fcm: Scalar<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the output circuit.
        pub fn from(
            state: console::program::State<A::Network>,
            randomizer: console::program::Randomizer<A::Network>,
            caller: console::account::Address<A::Network>,
            r_acm: A::ScalarField,
            r_fcm: A::ScalarField,
        ) -> Self {
            let state = State::<A>::new(Mode::Private, state);
            let randomizer = Randomizer::<A>::new(Mode::Private, randomizer);
            let caller = Address::<A>::new(Mode::Private, caller);
            let r_acm = Scalar::<A>::new(Mode::Private, r_acm);
            let r_fcm = Scalar::<A>::new(Mode::Private, r_fcm);

            Self { state, randomizer, caller, r_acm, r_fcm }
        }
    }

    pub struct OutputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> OutputCircuit<A> {
        /// Initializes the output circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { index, record, serial_numbers_digest, acm, fcm } = &public;
            ensure!(index.eject_mode().is_public(), "Output index must be public");
            ensure!(record.eject_mode().is_public(), "Output record must be public");
            ensure!(serial_numbers_digest.eject_mode().is_public(), "Serial numbers digest must be public");
            ensure!(acm.eject_mode().is_public(), "Address commitment must be public");
            ensure!(fcm.eject_mode().is_public(), "Fee commitment must be public");

            // Ensure all private members are private inputs.
            let Private { state, randomizer, caller, r_acm, r_fcm } = &private;
            ensure!(state.eject_mode().is_private(), "Output state must be private");
            ensure!(randomizer.eject_mode().is_private(), "Output randomizer must be private");
            ensure!(caller.eject_mode().is_private(), "Caller address must be private");
            ensure!(r_acm.eject_mode().is_private(), "Address randomizer must be private");
            ensure!(r_fcm.eject_mode().is_private(), "Fee randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the output circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Ensure the address commitment matches the declared caller.
            A::assert_eq(&public.acm, A::commit_bhp256(&private.caller.to_bits_le(), &private.r_acm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the fee commitment is correct.
            A::assert_eq(&public.fcm, A::commit_ped64(&U64::zero().to_bits_le(), &private.r_fcm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the randomizer is valid.
            A::assert(private.randomizer.verify(&private.caller, &public.serial_numbers_digest, &public.index));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Encrypt the program state into a record.
            let record = private.state.encrypt(&private.randomizer);
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the record matches the declared record.
            A::assert(record.is_equal(&public.record));
        }
    }
}

pub mod snark {
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
    use snarkvm_curves::{bls12_377::Bls12_377, PairingEngine};

    use anyhow::{ensure, Result};
    use std::time::Instant;

    type EC = Bls12_377;
    type Fq = <EC as PairingEngine>::Fq;
    type Fr = <EC as PairingEngine>::Fr;
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

        Ok(proof)
    }
}
