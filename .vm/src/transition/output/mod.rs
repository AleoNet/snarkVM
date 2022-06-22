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
    network::{prelude::*, Network},
    transition::{Record, State},
    types::{Field, Group, Scalar, U64},
};

pub struct Output<N: Network> {
    /// The output record.
    record: Record<N>,
    // /// The output program data.
    // data: Vec<Data<N>>,
}

impl<N: Network> Output<N> {
    /// Initializes a new `Output` for a transition.
    pub const fn new(record: Record<N>) -> Self {
        Self { record }
    }

    /// Returns the output record.
    pub const fn record(&self) -> &Record<N> {
        &self.record
    }

    /// Returns the balance commitment for the output record.
    pub const fn bcm(&self) -> Group<N> {
        self.record.bcm()
    }

    /// Returns the output commitment.
    pub fn to_commitment(&self) -> Result<Field<N>> {
        self.record.to_commitment()
    }
}

pub mod circuit {
    use circuit::{
        transition::Record,
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
