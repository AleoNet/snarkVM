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

use snarkvm_bytecode::{Identifier, Process, Program, Value};
use snarkvm_circuits::prelude::*;

pub struct HelloWorld;

impl HelloWorld {
    /// Initializes a new instance of `HelloWorld` with the given inputs.
    pub fn run<P: Program>(inputs: [Value<P>; 2]) -> Vec<Value<P>> {
        P::from_str(
            r"
function main:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;",
        );
        P::get_function(&Identifier::from_str("main")).unwrap().evaluate(&inputs)
    }
}

fn main() {
    let first = Value::from_str("1field.public");
    let second = Value::from_str("1field.private");

    let expected = Value::<Process>::from_str("2field.private");
    let candidate = HelloWorld::run::<Process>([first, second]);

    match (&expected, &candidate[0]) {
        (Value::Literal(Literal::Field(expected)), Value::Literal(Literal::Field(candidate))) => {
            println!("{candidate}");
            assert!(expected.is_equal(candidate).eject_value());
        }
        _ => panic!("Failed to load output"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hello_world() {
        let first = Value::from_str("1field.public");
        let second = Value::from_str("1field.private");

        let expected = Value::<Process>::from_str("2field.private");
        let candidate = HelloWorld::run::<Process>([first, second]);

        match (&expected, &candidate[0]) {
            (Value::Literal(Literal::Field(expected)), Value::Literal(Literal::Field(candidate))) => {
                assert!(expected.is_equal(candidate).eject_value())
            }
            _ => panic!("Failed to load output"),
        }
    }

    #[test]
    fn test_marlin() {
        pub struct HelloWorld;

        impl HelloWorld {
            /// Initializes a new instance of `HelloWorld` with the given inputs.
            pub fn run<P: Program>(inputs: &[Value<P>]) -> Vec<Value<P>> {
                P::from_str(
                    r"
function main:
    input r0 as u8.public;
    input r1 as u8.private;
    add r0 r1 into r2;
    output r2 as u8.private;",
                );
                P::get_function(&Identifier::from_str("main")).unwrap().evaluate(inputs)
            }
        }

        // Initialize the inputs.
        let input = [Value::from_str("1u8.public"), Value::from_str("1u8.private")];

        // Run the function.
        let _output = HelloWorld::run::<Process>(&input);

        // Marlin setup, prove, and verify.
        {
            use snarkvm_algorithms::{
                crypto_hash::PoseidonSponge,
                snark::marlin::{
                    ahp::AHPForR1CS,
                    fiat_shamir::FiatShamirAlgebraicSpongeRng,
                    MarlinHidingMode,
                    MarlinSNARK,
                },
            };
            use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
            use snarkvm_utilities::rand::test_rng;

            type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
            type MarlinInst = MarlinSNARK<Bls12_377, FS, MarlinHidingMode, Vec<Fr>>;

            let rng = &mut test_rng();

            let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(200, 200, 300).unwrap();
            let universal_srs = MarlinInst::universal_setup(max_degree, rng).unwrap();

            let (index_pk, index_vk) = MarlinInst::circuit_setup(&universal_srs, &Circuit).unwrap();
            println!("Called circuit setup");

            let proof = MarlinInst::prove(&index_pk, &Circuit, rng).unwrap();
            println!("Called prover");

            let zero = <Circuit as Environment>::BaseField::zero();
            let one = <Circuit as Environment>::BaseField::one();

            assert!(
                MarlinInst::verify(&index_vk, &[one, one, zero, zero, zero, zero, zero, zero, zero], &proof).unwrap()
            );
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInst::verify(&index_vk, &[one, one + one], &proof).unwrap());
        }
    }
}
