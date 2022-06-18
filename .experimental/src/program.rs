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

pub mod program {
    use circuit::{
        program::Record as RecordState,
        transition::Record,
        Address,
        Aleo,
        Ciphertext,
        Eject,
        Field,
        Group,
        Inject,
        Mode,
        Scalar,
        ToBits,
        ToField,
        ToGroup,
        U16,
    };

    use anyhow::{bail, ensure, Result};
    use itertools::Itertools;

    pub struct Public<A: Aleo> {
        /// The input serial numbers.
        serial_numbers: Vec<Field<A>>,
        /// The output records.
        output_records: Vec<Record<A>>,
        /// The output data.
        output_data: Vec<RecordState<A, Ciphertext<A>>>,
        /// The transition view key commitment (i.e. `tcm := Hash(caller, tpk, tvk)`).
        tcm: Field<A>,
        /// The transition public key (i.e. `tpk := Hash(r_tcm) * G`).
        tpk: Group<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the program circuit.
        pub fn from(
            serial_numbers: Vec<console::types::Field<A::Network>>,
            output_records: Vec<console::transition::Record<A::Network>>,
            output_data: Vec<console::program::Record<A::Network, console::program::Ciphertext<A::Network>>>,
            tcm: console::types::Field<A::Network>,
            tpk: console::types::Group<A::Network>,
        ) -> Self {
            Self {
                serial_numbers: Inject::new(Mode::Public, serial_numbers),
                output_records: Inject::new(Mode::Public, output_records),
                output_data: Inject::new(Mode::Public, output_data),
                tcm: Field::<A>::new(Mode::Public, tcm),
                tpk: Group::<A>::new(Mode::Public, tpk),
            }
        }
    }

    pub struct Private<A: Aleo> {
        /// The caller address.
        caller: Address<A>,
        /// The input record view keys.
        input_record_view_keys: Vec<Field<A>>,
        /// The input records.
        input_records: Vec<Record<A>>,
        /// The input data.
        input_data: Vec<RecordState<A, Ciphertext<A>>>,
        /// The transition view key commitment randomizer.
        r_tcm: Field<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the program circuit.
        pub fn from(
            caller: console::account::Address<A::Network>,
            record_view_keys: Vec<console::types::Field<A::Network>>,
            input_records: Vec<console::transition::Record<A::Network>>,
            input_data: Vec<console::program::Record<A::Network, console::program::Ciphertext<A::Network>>>,
            r_tcm: console::types::Field<A::Network>,
        ) -> Self {
            Self {
                caller: Address::new(Mode::Private, caller),
                input_record_view_keys: Inject::new(Mode::Private, record_view_keys),
                input_records: Inject::new(Mode::Private, input_records),
                input_data: Inject::new(Mode::Private, input_data),
                r_tcm: Field::<A>::new(Mode::Private, r_tcm),
            }
        }
    }

    pub struct ProgramCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> ProgramCircuit<A> {
        /// Initializes the program circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { serial_numbers, output_records, output_data, tcm, tpk } = &public;
            serial_numbers.iter().try_for_each(|serial_number| {
                ensure!(serial_number.eject_mode().is_public(), "Program serial number must be public");
                Ok(())
            })?;
            output_records.iter().zip_eq(output_data).try_for_each(|(output_record, output_data)| {
                ensure!(output_record.eject_mode().is_public(), "Program output record must be public");
                ensure!(output_data.eject_mode().is_public(), "Program output data must be public");
                Ok(())
            })?;
            ensure!(tcm.eject_mode().is_public(), "Transition view key commitment must be public");
            ensure!(tpk.eject_mode().is_public(), "Transition public key must be public");

            // Ensure all private members are private inputs.
            let Private { caller, input_record_view_keys, input_records, input_data, r_tcm } = &private;
            ensure!(caller.eject_mode().is_private(), "Caller must be private");
            input_record_view_keys.iter().zip_eq(input_records).zip_eq(input_data).try_for_each(
                |((record_view_key, record), data)| {
                    ensure!(record_view_key.eject_mode().is_private(), "Program record view key must be private");
                    ensure!(record.eject_mode().is_private(), "Program input record must be private");
                    ensure!(data.eject_mode().is_private(), "Program input data must be private");
                    Ok(())
                },
            )?;
            ensure!(r_tcm.eject_mode().is_private(), "Transition view key commitment randomizer must be private");

            Ok(Self(public, private))
        }

        /// Executes the program circuit.
        pub fn execute(&self) {
            let (public, private) = (&self.0, &self.1);

            // Initialize a vector for the inputs.
            let mut inputs = Vec::with_capacity(private.input_records.len());

            // Ensure all of the inputs are well-formed.
            for ((record, record_view_key), data) in
                private.input_records.iter().zip_eq(&private.input_record_view_keys).zip_eq(&private.input_data)
            {
                // Compute the record commitment.
                let _commitment = record.to_commitment();
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Ensure the serial number matches the declared serial number.
                // A::assert_eq(&public.serial_number, private.serial_number.value());
                // println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
                // // Ensure the serial number is valid.
                // A::assert(private.serial_number.verify(state.owner(), &[], &commitment));
                // println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Decrypt the record into program state.
                let state = record.decrypt_symmetric(record_view_key);
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Ensure the caller is the owner of the record.
                A::assert_eq(&private.caller, state.owner());
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Compute the data ID.
                let data_id = data.to_id();
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Ensure the data ID matches the declared data ID in the record.
                A::assert_eq(&data_id, record.data());
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Ensure the data ID matches the declared data ID in the state.
                A::assert_eq(&data_id, state.data());
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Compute the data view key from the record view key.
                let data_randomizer = &A::hash_many_psd2(&[A::encryption_domain(), record_view_key.clone()], 3)[2];
                let data_view_key = record_view_key * data_randomizer;
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Decrypt the ciphertext data into plaintext data.
                let data = data.decrypt_symmetric(data_view_key);
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Append the state and data to the inputs.
                inputs.push((state, data));
            }

            // Compute the transition secret key `tsk` as `HashToScalar(r_tcm)`.
            let tsk = A::hash_to_scalar_psd2(&[private.r_tcm.clone()]);
            // Ensure the transition public key `tpk` is `tsk * G`.
            A::assert_eq(&public.tpk, &A::g_scalar_multiply(&tsk));

            // Compute the transition view key `tvk` as `tsk * caller`.
            let tvk = private.caller.to_group() * tsk;
            // Ensure the transition view key commitment `tcm` is `Hash(caller, tpk, tvk)`.
            let preimage = [&private.caller.to_group(), &public.tpk, &tvk].map(|c| c.to_x_coordinate());
            A::assert_eq(&public.tcm, &A::hash_psd4(&preimage));
            println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

            // // Execute the function.
            // let (output_states, output_data) = A::transition(inputs);
            //
            // // Ensure all of the outputs are well-formed.
            // for (index, (record, record_view_key)) in public.output_records.iter().zip_eq(&public.output_data).enumerate() {
            //     // Compute the encryption randomizer as `HashToScalar(tvk || index)`.
            //     let randomizer = A::hash_to_scalar_psd2(&[tvk.to_x_coordinate(), U16::constant(index as u16).to_field()]);
            //     // Encrypt the program state into a record, using the randomizer.
            //     let record = private.state.encrypt(&randomizer);
            //     // Ensure the record matches the declared record.
            //     A::assert(public.record.is_equal(&record));
            //     println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
            //
            //
            //     // Compute the record commitment.
            //     let commitment = record.to_commitment();
            //     println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
            //
            //     // Ensure the serial number matches the declared serial number.
            //     // A::assert_eq(&public.serial_number, private.serial_number.value());
            //     // println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
            //     // // Ensure the serial number is valid.
            //     // A::assert(private.serial_number.verify(state.owner(), &[], &commitment));
            //     // println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
            //
            //     // Decrypt the record into program state.
            //     let state = record.decrypt_symmetric(&record_view_key);
            //     println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
            //
            //     // Append the state to the outputs.
            //     outputs.push(state);
            // }
        }
    }
}
