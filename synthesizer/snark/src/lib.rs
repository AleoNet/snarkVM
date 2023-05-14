// Copyright (C) 2019-2023 Aleo Systems Inc.
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
#![allow(clippy::too_many_arguments)]
#![warn(clippy::cast_possible_truncation)]
#![cfg_attr(not(feature = "aleo-cli"), allow(unused_variables))]

use console::network::{prelude::*, FiatShamir};
use snarkvm_algorithms::{snark::marlin, traits::SNARK};

use once_cell::sync::OnceCell;
use std::sync::Arc;

#[cfg(feature = "aleo-cli")]
use colored::Colorize;

type Marlin<N> = marlin::MarlinSNARK<<N as Environment>::PairingCurve, FiatShamir<N>, marlin::MarlinHidingMode>;

mod certificate;
pub use certificate::Certificate;

mod proof;
pub use proof::Proof;

mod proving_key;
pub use proving_key::ProvingKey;

mod universal_srs;
pub use universal_srs::UniversalSRS;

mod verifying_key;
pub use verifying_key::VerifyingKey;

#[cfg(test)]
pub(crate) mod test_helpers {
    use super::*;
    use circuit::prelude::{Assignment, Circuit, Eject, Environment, Field, Inject, Mode, NumOne, One};
    use console::network::Testnet3;

    use once_cell::sync::OnceCell;

    type CurrentNetwork = Testnet3;

    /// Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
    fn create_example_circuit<E: Environment>() -> Field<E> {
        let one = console::types::Field::<E::Network>::one();
        let two = one + one;

        const EXPONENT: u64 = 64;

        // Compute 2^EXPONENT - 1, in a purposefully constraint-inefficient manner for testing.
        let mut candidate = Field::<E>::new(Mode::Public, one);
        let mut accumulator = Field::new(Mode::Private, two);
        for _ in 0..EXPONENT {
            candidate += &accumulator;
            accumulator *= Field::new(Mode::Private, two);
        }

        assert_eq!((accumulator - Field::one()).eject_value(), candidate.eject_value());
        assert_eq!(2, E::num_public());
        assert_eq!(2 * EXPONENT + 1, E::num_private());
        assert_eq!(EXPONENT, E::num_constraints());
        assert!(E::is_satisfied());

        candidate
    }

    /// Returns a sample assignment for the example circuit.
    pub(crate) fn sample_assignment() -> Assignment<<Circuit as Environment>::BaseField> {
        static INSTANCE: OnceCell<Assignment<<Circuit as Environment>::BaseField>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                let _candidate_output = create_example_circuit::<Circuit>();
                let assignment = Circuit::eject_assignment_and_reset();
                assert_eq!(0, Circuit::num_constants());
                assert_eq!(1, Circuit::num_public());
                assert_eq!(0, Circuit::num_private());
                assert_eq!(0, Circuit::num_constraints());
                assignment
            })
            .clone()
    }

    /// Returns the sample circuit keys for the example circuit.
    pub(crate) fn sample_keys() -> (ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>) {
        static INSTANCE: OnceCell<(ProvingKey<CurrentNetwork>, VerifyingKey<CurrentNetwork>)> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                let assignment = sample_assignment();
                let srs = UniversalSRS::load().unwrap();
                let (proving_key, verifying_key) = srs.to_circuit_key("test", &assignment).unwrap();
                (proving_key, verifying_key)
            })
            .clone()
    }

    /// Returns a sample proof for the example circuit.
    pub(crate) fn sample_proof() -> Proof<CurrentNetwork> {
        static INSTANCE: OnceCell<Proof<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                let assignment = sample_assignment();
                let (proving_key, _) = sample_keys();
                proving_key.prove("test", &assignment, &mut TestRng::default()).unwrap()
            })
            .clone()
    }

    /// Returns a sample certificate for the example circuit.
    pub(super) fn sample_certificate() -> Certificate<CurrentNetwork> {
        static INSTANCE: OnceCell<Certificate<CurrentNetwork>> = OnceCell::new();
        INSTANCE
            .get_or_init(|| {
                let (proving_key, verifying_key) = sample_keys();
                // Return the certificate.
                Certificate::certify("test", &proving_key, &verifying_key).unwrap()
            })
            .clone()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use circuit::prelude::{Circuit, Environment, NumOne};
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_marlin() {
        let assignment = crate::test_helpers::sample_assignment();

        // Marlin setup, prove, and verify.
        let srs = UniversalSRS::<CurrentNetwork>::load().unwrap();
        let (proving_key, verifying_key) = srs.to_circuit_key("test", &assignment).unwrap();
        println!("Called circuit setup");

        let proof = proving_key.prove("test", &assignment, &mut TestRng::default()).unwrap();
        println!("Called prover");

        let one = <Circuit as Environment>::BaseField::one();
        assert!(verifying_key.verify("test", &[one, one], &proof));
        println!("Called verifier");
        println!("\nShould not verify (i.e. verifier messages should print below):");
        assert!(!verifying_key.verify("test", &[one, one + one], &proof));
    }
}
