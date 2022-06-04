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
    use circuit::{Aleo, Ciphertext, Data, Eject, Field, Inject, Mode, Record, Scalar, ToBits};

    use anyhow::{ensure, Result};
    use itertools::Itertools;

    pub struct Public<A: Aleo> {
        /// The input serial numbers.
        serial_numbers: Vec<Field<A>>,
        /// The output records.
        output_records: Vec<Record<A>>,
        /// The output data.
        output_data: Vec<Data<A, Ciphertext<A>>>,
        /// The address commitment (i.e. `acm := Commit(caller, r_acm)`).
        acm: Field<A>,
    }

    impl<A: Aleo> Public<A> {
        /// Initializes the public inputs for the program circuit.
        pub fn from(
            serial_numbers: Vec<A::BaseField>,
            output_records: Vec<console::program::Record<A::Network>>,
            output_data: Vec<console::program::Data<A::Network, console::program::Ciphertext<A::Network>>>,
            acm: A::BaseField,
        ) -> Self {
            Self {
                serial_numbers: Inject::new(Mode::Public, serial_numbers),
                output_records: Inject::new(Mode::Public, output_records),
                output_data: Inject::new(Mode::Public, output_data),
                acm: Field::<A>::new(Mode::Public, acm),
            }
        }
    }

    pub struct Private<A: Aleo> {
        /// The input record view keys.
        input_record_view_keys: Vec<Field<A>>,
        /// The input records.
        input_records: Vec<Record<A>>,
        /// The input data.
        input_data: Vec<Data<A, Ciphertext<A>>>,
        /// The address randomizer.
        r_acm: Scalar<A>,
    }

    impl<A: Aleo> Private<A> {
        /// Initializes the private inputs for the program circuit.
        pub fn from(
            record_view_keys: Vec<A::BaseField>,
            input_records: Vec<console::program::Record<A::Network>>,
            input_data: Vec<console::program::Data<A::Network, console::program::Ciphertext<A::Network>>>,
            r_acm: A::ScalarField,
        ) -> Self {
            Self {
                input_record_view_keys: Inject::new(Mode::Private, record_view_keys),
                input_records: Inject::new(Mode::Private, input_records),
                input_data: Inject::new(Mode::Private, input_data),
                r_acm: Scalar::<A>::new(Mode::Private, r_acm),
            }
        }
    }

    pub struct ProgramCircuit<A: Aleo>(Public<A>, Private<A>);

    impl<A: Aleo> ProgramCircuit<A> {
        /// Initializes the program circuit.
        pub fn from(public: Public<A>, private: Private<A>) -> Result<Self> {
            // Ensure all public members are public inputs.
            let Public { serial_numbers, output_records, output_data, acm } = &public;
            serial_numbers.iter().try_for_each(|serial_number| {
                Ok(ensure!(serial_number.eject_mode().is_public(), "Program serial number must be public"))
            })?;
            output_records.iter().try_for_each(|output_record| {
                Ok(ensure!(output_record.eject_mode().is_public(), "Program output record must be public"))
            })?;
            output_data.iter().try_for_each(|output_data| {
                Ok(ensure!(output_data.eject_mode().is_public(), "Program output data must be public"))
            })?;
            ensure!(acm.eject_mode().is_public(), "Address commitment must be public");

            // Ensure all private members are private inputs.
            let Private { input_record_view_keys, input_records, input_data, r_acm } = &private;
            input_record_view_keys.iter().try_for_each(|record_view_key| {
                Ok(ensure!(record_view_key.eject_mode().is_private(), "Program record view key must be private"))
            })?;
            input_records.iter().try_for_each(|record| {
                Ok(ensure!(record.eject_mode().is_private(), "Program input record must be private"))
            })?;
            input_data.iter().try_for_each(|data| {
                Ok(ensure!(data.eject_mode().is_private(), "Program input data must be private"))
            })?;
            ensure!(r_acm.eject_mode().is_private(), "Address randomizer must be private");

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
                let state = record.decrypt_symmetric(&record_view_key);
                println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());

                // Ensure the address commitment matches the state owner.
                A::assert_eq(&public.acm, A::commit_bhp256(&state.owner().to_bits_le(), &private.r_acm));
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

            // // Ensure all of the outputs are well-formed.
            // for (record, record_view_key) in public.output_records.iter().zip_eq(&public.output_data) {
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
            //     // Ensure the address commitment matches the state owner.
            //     A::assert_eq(&public.acm, A::commit_bhp256(&state.owner().to_bits_le(), &private.r_acm));
            //     println!("Is satisfied? {} ({} constraints)", A::is_satisfied(), A::num_constraints());
            //
            //     // Append the state to the outputs.
            //     outputs.push(state);
            // }
        }
    }
}
