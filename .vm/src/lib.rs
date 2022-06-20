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
#![allow(clippy::module_inception)]

#[allow(dead_code, unused_imports)]
mod program_circuit;
pub use program_circuit::*;

mod process;
pub use process::*;

mod program;
pub use program::*;

pub mod input {
    use circuit::{
        Aleo,
        Eject,
        Field,
        Group,
        Inject,
        merkle_tree::MerklePath,
        Mode,
        Scalar,
        SerialNumber,
        ToBits,
        ToGroup,
        transition::Record,
        U64,
        Zero,
    };

    use anyhow::{ensure, Result};

    pub struct Public<A: Aleo> {
        /// The input program root.
        root: Field<A>,
        /// The input serial number.
        serial_number: Field<A>,
        /// The re-randomized balance commitment (i.e. `bcm := Commit(balance, r_bcm + r_bcm')`).
        bcm: Group<A>,
        /// The fee commitment (i.e. `fcm := Σ bcm_in - Σ bcm_out - Commit(fee, 0) = Commit(0, r_fcm)`).
        fcm: Group<A>,
        /// The transition view key commitment (i.e. `tcm := Hash(caller, tpk, tvk)`).
        tcm: Field<A>,
        /// The transition public key (i.e. `tpk := Hash(r_tcm) * G`).
        tpk: Group<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the input circuit.
        pub fn from(
            root: console::types::Field<A::Network>,
            serial_number: console::types::Field<A::Network>,
            bcm: console::types::Group<A::Network>,
            fcm: console::types::Group<A::Network>,
            tcm: console::types::Field<A::Network>,
            tpk: console::types::Group<A::Network>,
        ) -> Self {
            Self {
                root: Field::new(Mode::Public, root),
                serial_number: Field::new(Mode::Public, serial_number),
                bcm: Group::new(Mode::Public, bcm),
                fcm: Group::new(Mode::Public, fcm),
                tcm: Field::new(Mode::Public, tcm),
                tpk: Group::new(Mode::Public, tpk),
            }
        }
    }

    pub struct Private<A: Aleo> {
        /// The input record view key.
        record_view_key: Field<A>,
        /// The input record.
        record: Record<A>,
        /// The input commitment Merkle path.
        merkle_path: MerklePath<A, 32>,
        /// The input serial number signature.
        serial_number: SerialNumber<A>,
        /// The fee randomizer (i.e. `r_fcm := Σ r_in - Σ r_out`).
        r_fcm: Scalar<A>,
        /// The transition view key commitment randomizer.
        r_tcm: Field<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the input circuit.
        pub fn from(
            record_view_key: console::types::Field<A::Network>,
            record: console::transition::Record<A::Network>,
            merkle_path: console::collections::merkle_tree::MerklePath<A::Network, 32>,
            serial_number: console::transition::SerialNumber<A::Network>,
            r_fcm: console::types::Scalar<A::Network>,
            r_tcm: console::types::Field<A::Network>,
        ) -> Self {
            Self {
                record_view_key: Field::new(Mode::Private, record_view_key),
                record: Record::new(Mode::Private, record),
                merkle_path: MerklePath::new(Mode::Private, merkle_path),
                serial_number: SerialNumber::new(Mode::Private, serial_number),
                r_fcm: Scalar::new(Mode::Private, r_fcm),
                r_tcm: Field::new(Mode::Private, r_tcm),
            }
        }
    }

    pub struct InputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> InputCircuit<A> {
        /// Initializes the input circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { root, serial_number, bcm, fcm, tcm, tpk } = &public;
            ensure!(root.eject_mode().is_public(), "Input root must be public");
            ensure!(serial_number.eject_mode().is_public(), "Input serial number must be public");
            ensure!(bcm.eject_mode().is_public(), "Balance commitment must be public");
            ensure!(fcm.eject_mode().is_public(), "Fee commitment must be public");
            ensure!(tcm.eject_mode().is_public(), "Transition view key commitment must be public");
            ensure!(tpk.eject_mode().is_public(), "Transition public key must be public");

            // Ensure all private members are private inputs.
            let Private { record_view_key, record, merkle_path, serial_number, r_fcm, r_tcm } = &private;
            ensure!(record_view_key.eject_mode().is_private(), "Input record view key must be private");
            ensure!(record.eject_mode().is_private(), "Input record must be private");
            ensure!(merkle_path.eject_mode().is_private(), "Input commitment Merkle path must be private");
            ensure!(serial_number.eject_mode().is_private(), "Input serial number proof must be private");
            ensure!(r_fcm.eject_mode().is_private(), "Fee randomizer must be private");
            ensure!(r_tcm.eject_mode().is_private(), "Transition view key commitment randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the input circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Decrypt the record into program state.
            let state = private.record.decrypt_symmetric(&private.record_view_key);
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Compute the transition secret key `tsk` as `HashToScalar(r_tcm)`.
            let tsk = A::hash_to_scalar_psd2(&[private.r_tcm.clone()]);
            // Ensure the transition public key `tpk` is `tsk * G`.
            A::assert_eq(&public.tpk, &A::g_scalar_multiply(&tsk));

            // Compute the transition view key `tvk` as `tsk * caller`.
            let tvk = state.owner().to_group() * tsk;
            // Ensure the transition view key commitment `tcm` is `Hash(caller, tpk, tvk)`.
            let preimage = [&state.owner().to_group(), &public.tpk, &tvk].map(|c| c.to_x_coordinate());
            A::assert_eq(&public.tcm, &A::hash_psd4(&preimage));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Compute the re-randomizer for the balance commitment (i.e. HashToScalar(G^r^view_key));
            let r_bcm = A::hash_to_scalar_psd2(&[A::r_bcm_domain(), private.record_view_key.clone()]);
            // Ensure the randomized balance commitment is based on the original balance commitment.
            A::assert_eq(&public.bcm, private.record.bcm() + &A::commit_ped64(&U64::zero().to_bits_le(), &r_bcm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the fee commitment is correct.
            A::assert_eq(&public.fcm, A::commit_ped64(&U64::zero().to_bits_le(), &private.r_fcm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Compute the record commitment.
            let commitment = private.record.to_commitment();
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the commitment exists in the Merkle path.
            A::assert(A::verify_merkle_path_bhp(&private.merkle_path, &public.root, &commitment.to_bits_le()));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the serial number is valid.
            A::assert(private.serial_number.verify(state.owner(), &[], &commitment));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the serial number matches the declared serial number.
            A::assert_eq(&public.serial_number, private.serial_number.value());
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
        Scalar,
        State,
        ToBits,
        ToField,
        ToGroup,
        transition::Record,
        U16,
        U64,
        Zero,
    };

    use anyhow::{ensure, Result};

    pub struct Public<A: Aleo> {
        /// The output index.
        index: U16<A>,
        /// The output record.
        record: Record<A>,
        /// The fee commitment (i.e. `fcm := Σ bcm_in - Σ bcm_out - Commit(fee, 0) = Commit(0, r_fcm)`).
        fcm: Group<A>,
        /// The transition view key commitment (i.e. `tcm := Hash(caller, tpk, tvk)`).
        tcm: Field<A>,
        /// The transition public key (i.e. `tpk := Hash(r_tcm) * G`).
        tpk: Group<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the output circuit.
        pub fn from(
            index: u16,
            record: console::transition::Record<A::Network>,
            fcm: console::types::Group<A::Network>,
            tcm: console::types::Field<A::Network>,
            tpk: console::types::Group<A::Network>,
        ) -> Self {
            Self {
                index: U16::new(Mode::Public, console::types::U16::new(index)),
                record: Record::new(Mode::Public, record),
                fcm: Group::new(Mode::Public, fcm),
                tcm: Field::new(Mode::Public, tcm),
                tpk: Group::new(Mode::Public, tpk),
            }
        }
    }

    pub struct Private<A: Aleo> {
        /// The caller address.
        caller: Address<A>,
        /// The output state.
        state: State<A>,
        /// The fee randomizer (i.e. `r_fcm := Σ r_in - Σ r_out`).
        r_fcm: Scalar<A>,
        /// The transition view key commitment randomizer.
        r_tcm: Field<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the output circuit.
        pub fn from(
            caller: console::account::Address<A::Network>,
            state: console::transition::State<A::Network>,
            r_fcm: console::types::Scalar<A::Network>,
            r_tcm: console::types::Field<A::Network>,
        ) -> Self {
            Self {
                caller: Address::new(Mode::Private, caller),
                state: State::new(Mode::Private, state),
                r_fcm: Scalar::new(Mode::Private, r_fcm),
                r_tcm: Field::new(Mode::Private, r_tcm),
            }
        }
    }

    pub struct OutputCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> OutputCircuit<A> {
        /// Initializes the output circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { index, record, fcm, tcm, tpk } = &public;
            ensure!(index.eject_mode().is_public(), "Output index must be public");
            ensure!(record.eject_mode().is_public(), "Output record must be public");
            ensure!(fcm.eject_mode().is_public(), "Fee commitment must be public");
            ensure!(tcm.eject_mode().is_public(), "Transition view key commitment must be public");
            ensure!(tpk.eject_mode().is_public(), "Transition public key must be public");

            // Ensure all private members are private inputs.
            let Private { caller, state, r_fcm, r_tcm } = &private;
            ensure!(caller.eject_mode().is_private(), "Caller address must be private");
            ensure!(state.eject_mode().is_private(), "Output state must be private");
            ensure!(r_fcm.eject_mode().is_private(), "Fee randomizer must be private");
            ensure!(r_tcm.eject_mode().is_private(), "Transition view key commitment randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the output circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Compute the transition secret key `tsk` as `HashToScalar(r_tcm)`.
            let tsk = A::hash_to_scalar_psd2(&[private.r_tcm.clone()]);
            // Ensure the transition public key `tpk` is `tsk * G`.
            A::assert_eq(&public.tpk, &A::g_scalar_multiply(&tsk));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Compute the transition view key `tvk` as `tsk * caller`.
            let tvk = private.caller.to_group() * tsk;
            // Ensure the transition view key commitment `tcm` is `Hash(caller, tpk, tvk)`.
            let preimage = [&private.caller.to_group(), &public.tpk, &tvk].map(|c| c.to_x_coordinate());
            A::assert_eq(&public.tcm, &A::hash_psd4(&preimage));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
            let randomizer = A::hash_to_scalar_psd2(&[tvk.to_x_coordinate(), public.index.to_field()]);
            // Encrypt the program state into a record, using the randomizer.
            let record = private.state.encrypt(&randomizer);
            // Ensure the record matches the declared record.
            A::assert(public.record.is_equal(&record));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // Ensure the fee commitment is correct.
            A::assert_eq(&public.fcm, A::commit_ped64(&U64::zero().to_bits_le(), &private.r_fcm));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
        }
    }
}

pub mod snark {
    use snarkvm_algorithms::{
        crypto_hash::PoseidonSponge,
        SNARK,
        snark::marlin::{
            ahp::AHPForR1CS,
            fiat_shamir::FiatShamirAlgebraicSpongeRng,
            MarlinHidingMode,
            MarlinSNARK,
            Proof,
        },
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
