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
    network::Network,
    types::{Field, Group},
};

pub struct Input<N: Network> {
    /// The serial number of the input record.
    serial_number: Field<N>,
    /// The re-randomized balance commitment (i.e. `bcm := Commit(balance, r_bcm + r_bcm')`).
    bcm: Group<N>,
}

impl<N: Network> Input<N> {
    /// Initializes a new `Input` for a transition.
    pub const fn new(serial_number: Field<N>, bcm: Group<N>) -> Self {
        Self { serial_number, bcm }
    }

    /// Returns the serial number of the input record.
    pub const fn serial_number(&self) -> Field<N> {
        self.serial_number
    }

    /// Returns the balance commitment for the input record.
    pub const fn bcm(&self) -> Group<N> {
        self.bcm
    }
}

pub mod circuit {
    use circuit::{
        merkle_tree::MerklePath,
        transition::Record,
        Aleo,
        Eject,
        Field,
        Group,
        Inject,
        Mode,
        Scalar,
        SerialNumber,
        ToBits,
        ToGroup,
        Zero,
        U64,
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
