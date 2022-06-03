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
        U16,
    };

    use anyhow::{ensure, Result};

    pub struct Public<A: Aleo> {
        /// The output index.
        index: U16<A>,
        /// The output record.
        record: Record<A>,
        /// The serial numbers digest.
        serial_numbers_digest: Field<A>,
        /// The address commitment (i.e. `acm := Commit(caller, randomizer)`).
        acm: Field<A>,
        /// The balance commitment (i.e. `bcm := (Σ bcm_in - Σ bcm_out - Commit(fee, 0))`).
        bcm: Field<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the output circuit.
        pub fn from(
            index: u16,
            record: console::program::Record<A::Network>,
            serial_numbers_digest: A::BaseField,
            acm: A::BaseField,
            bcm: A::BaseField,
        ) -> Self {
            let index = U16::<A>::new(Mode::Public, index);
            let record = Record::<A>::new(Mode::Public, record);
            let serial_numbers_digest = Field::<A>::new(Mode::Public, serial_numbers_digest);
            let acm = Field::<A>::new(Mode::Public, acm);
            let bcm = Field::<A>::new(Mode::Public, bcm);

            Self { index, record, serial_numbers_digest, acm, bcm }
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
        /// The balance randomizer (i.e. `r_bcm := Σ r_in - Σ r_out`).
        r_bcm: Scalar<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the output circuit.
        pub fn from(
            state: console::program::State<A::Network>,
            randomizer: console::program::Randomizer<A::Network>,
            caller: console::account::Address<A::Network>,
            r_acm: A::ScalarField,
            r_bcm: A::ScalarField,
        ) -> Self {
            let state = State::<A>::new(Mode::Private, state);
            let randomizer = Randomizer::<A>::new(Mode::Private, randomizer);
            let caller = Address::<A>::new(Mode::Private, caller);
            let r_acm = Scalar::<A>::new(Mode::Private, r_acm);
            let r_bcm = Scalar::<A>::new(Mode::Private, r_bcm);

            Self { state, randomizer, caller, r_acm, r_bcm }
        }
    }

    pub struct OutputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> OutputCircuit<A> {
        /// Initializes the output circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { index, record, serial_numbers_digest, acm, bcm } = &public;
            ensure!(index.eject_mode().is_public(), "Output index must be public");
            ensure!(record.eject_mode().is_public(), "Output record must be public");
            ensure!(serial_numbers_digest.eject_mode().is_public(), "Serial numbers digest must be public");
            ensure!(acm.eject_mode().is_public(), "Address commitment must be public");
            ensure!(bcm.eject_mode().is_public(), "Balance commitment must be public");

            // Ensure all private members are private inputs.
            let Private { state, randomizer, caller, r_acm, r_bcm } = &private;
            ensure!(state.eject_mode().is_private(), "Output state must be private");
            ensure!(randomizer.eject_mode().is_private(), "Output randomizer must be private");
            ensure!(caller.eject_mode().is_private(), "Caller address must be private");
            ensure!(r_acm.eject_mode().is_private(), "Address randomizer must be private");
            ensure!(r_bcm.eject_mode().is_private(), "Balance randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the output circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Ensure the address commitment matches the declared caller.
            A::assert_eq(&public.acm, A::commit_bhp256(&private.caller.to_bits_le(), &private.r_acm));
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
