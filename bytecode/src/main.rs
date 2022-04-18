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

use snarkvm_bytecode::{Function, Identifier, Process, Program, Value};
use snarkvm_circuits::prelude::*;

pub struct HelloWorld;

impl HelloWorld {
    /// Initializes a new instance of `HelloWorld`.
    pub fn initialize<P: Program>() {
        P::from_str(
            r"
function main:
    input r0 as field.public;
    input r1 as field.private;
    add r0 r1 into r2;
    output r2 as field.private;",
        );
    }

    /// Runs `HelloWorld` with the given inputs.
    pub fn run<P: Program>(inputs: [Value<P>; 2]) -> Vec<Value<P>> {
        P::get_function(&Identifier::from_str("main")).unwrap().evaluate(&inputs)
    }

    /// Returns an estimated cost of running `HelloWorld`.
    pub fn count<P: Program>() -> CircuitCount {
        Function::count(&P::get_function(&Identifier::from_str("main")).unwrap())
    }
}

fn main() {
    // Initialize the program.
    HelloWorld::initialize::<Process>();

    // Get estimated circuit count for the `HelloWorld` program.
    let count = HelloWorld::count::<Process>();

    // Run the `HelloWorld` program with the given inputs.
    let first = Value::from_str("1field.public");
    let second = Value::from_str("1field.private");

    // Store the circuit counts before running the program.
    let old_num_constants = <Process as Program>::Aleo::num_constants();
    let old_num_public = <Process as Program>::Aleo::num_public();
    let old_num_private = <Process as Program>::Aleo::num_private();
    let old_num_constraints = <Process as Program>::Aleo::num_constraints();

    let candidate = HelloWorld::run::<Process>([first, second]);

    // Store the circuit counts after running the program.
    let new_num_constants = <Process as Program>::Aleo::num_constants();
    let new_num_public = <Process as Program>::Aleo::num_public();
    let new_num_private = <Process as Program>::Aleo::num_private();
    let new_num_constraints = <Process as Program>::Aleo::num_constraints();

    // Check that the estimated counts is correct.
    assert!(count.is_satisfied(
        new_num_constants - old_num_constants,
        new_num_public - old_num_public,
        new_num_private - old_num_private,
        new_num_constraints - old_num_constraints
    ));

    let expected = Value::<Process>::from_str("2field.private");

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
        // Initialize the program.
        HelloWorld::initialize::<Process>();

        // Get estimated circuit count for the `HelloWorld` program.
        let count = HelloWorld::count::<Process>();

        // Run the `HelloWorld` program with the given inputs.
        let first = Value::from_str("1field.public");
        let second = Value::from_str("1field.private");

        // Store the circuit counts before running the program.
        let old_num_constants = <Process as Program>::Aleo::num_constants();
        let old_num_public = <Process as Program>::Aleo::num_public();
        let old_num_private = <Process as Program>::Aleo::num_private();
        let old_num_constraints = <Process as Program>::Aleo::num_constraints();

        let candidate = HelloWorld::run::<Process>([first, second]);

        // Store the circuit counts after running the program.
        let new_num_constants = <Process as Program>::Aleo::num_constants();
        let new_num_public = <Process as Program>::Aleo::num_public();
        let new_num_private = <Process as Program>::Aleo::num_private();
        let new_num_constraints = <Process as Program>::Aleo::num_constraints();

        // Check that the estimated counts is correct.
        assert!(count.is_satisfied(
            new_num_constants - old_num_constants,
            new_num_public - old_num_public,
            new_num_private - old_num_private,
            new_num_constraints - old_num_constraints
        ));

        let expected = Value::<Process>::from_str("2field.private");

        match (&expected, &candidate[0]) {
            (Value::Literal(Literal::Field(expected)), Value::Literal(Literal::Field(candidate))) => {
                println!("{candidate}");
                assert!(expected.is_equal(candidate).eject_value());
            }
            _ => panic!("Failed to load output"),
        }
    }

    #[test]
    fn test_marlin() {
        pub struct HelloWorld;

        impl HelloWorld {
            /// Initializes a new instance of the `HelloWorld` program.
            pub fn initialize<P: Program>() {
                P::from_str(
                    r"
function main:
    input r0 as u8.public;
    input r1 as u8.private;
    add r0 r1 into r2;
    output r2 as u8.private;",
                );
            }

            /// Runs the `HelloWorld` with the given inputs.
            pub fn run<P: Program>(inputs: &[Value<P>]) -> Vec<Value<P>> {
                P::get_function(&Identifier::from_str("main")).unwrap().evaluate(inputs)
            }

            /// Estimates the circuit counts for the `HelloWorld` program.
            pub fn count<P: Program>() -> CircuitCount {
                Function::count(&P::get_function(&Identifier::from_str("main")).unwrap())
            }
        }

        // Initialize the program.
        HelloWorld::initialize::<Process>();

        // Get estimated circuit count for the `HelloWorld` program.
        let count = HelloWorld::count::<Process>();

        // Initialize the inputs.
        let input = [Value::from_str("1u8.public"), Value::from_str("1u8.private")];

        // Store the circuit counts before running the program.
        let old_num_constants = <Process as Program>::Aleo::num_constants();
        let old_num_public = <Process as Program>::Aleo::num_public();
        let old_num_private = <Process as Program>::Aleo::num_private();
        let old_num_constraints = <Process as Program>::Aleo::num_constraints();

        // Run the function.
        let _output = HelloWorld::run::<Process>(&input);

        // Store the circuit counts after running the program.
        let new_num_constants = <Process as Program>::Aleo::num_constants();
        let new_num_public = <Process as Program>::Aleo::num_public();
        let new_num_private = <Process as Program>::Aleo::num_private();
        let new_num_constraints = <Process as Program>::Aleo::num_constraints();

        // Check that the estimated counts is correct.
        assert!(count.is_satisfied(
            new_num_constants - old_num_constants,
            new_num_public - old_num_public,
            new_num_private - old_num_private,
            new_num_constraints - old_num_constraints
        ));

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

    #[test]
    fn test_silly_sudoku() {
        pub struct SillySudoku;

        impl SillySudoku {
            /// Initializes a new instance of the `HelloWorld` program.
            pub fn initialize<P: Program>() {
                P::from_str(
                    r"
function main:
    input r0 as u8.private;
    input r1 as u8.private;
    input r2 as u8.private;
    input r3 as u8.private;
    input r4 as u8.private;
    input r5 as u8.private;
    input r6 as u8.private;
    input r7 as u8.private;
    input r8 as u8.private;
    add r0 r1 into r9;
    add r2 r3 into r10;
    add r4 r5 into r11;
    add r6 r7 into r12;
    add r9 r10 into r13;
    add r11 r12 into r14;
    add r13 r14 into r15;
    add r15 r8 into r16;
    eq r16 45u8 into r17;
    output r17 as boolean.private;",
                );
            }

            /// Runs the `SillySudoku` with the given inputs.
            pub fn run<P: Program>(inputs: &[Value<P>]) -> Vec<Value<P>> {
                P::get_function(&Identifier::from_str("main")).unwrap().evaluate(inputs)
            }

            /// Estimates the circuit counts for the `SillySudoku` program.
            pub fn count<P: Program>() -> CircuitCount {
                Function::count(&P::get_function(&Identifier::from_str("main")).unwrap())
            }
        }

        // Initialize the program.
        SillySudoku::initialize::<Process>();

        // Get estimated circuit count for the `SillySudoku` program.
        // This function produces 0 constants, 0 public variables, 74 private variables, and 91 constraints.
        let count = SillySudoku::count::<Process>();

        // Run the `HelloWorld` program with the given inputs.
        let first = Value::<Process>::from_str("1u8.private");
        let second = Value::<Process>::from_str("1u8.private");
        let third = Value::<Process>::from_str("1u8.private");
        let fourth = Value::<Process>::from_str("1u8.private");
        let fifth = Value::<Process>::from_str("1u8.private");
        let sixth = Value::<Process>::from_str("1u8.private");
        let seventh = Value::<Process>::from_str("1u8.private");
        let eighth = Value::<Process>::from_str("1u8.private");
        let ninth = Value::<Process>::from_str("1u8.private");

        // Store the circuit counts before running the program.
        let old_num_constants = <Process as Program>::Aleo::num_constants();
        let old_num_public = <Process as Program>::Aleo::num_public();
        let old_num_private = <Process as Program>::Aleo::num_private();
        let old_num_constraints = <Process as Program>::Aleo::num_constraints();

        let candidate =
            SillySudoku::run::<Process>(&[first, second, third, fourth, fifth, sixth, seventh, eighth, ninth]);

        // Store the circuit counts after running the program.
        let new_num_constants = <Process as Program>::Aleo::num_constants();
        let new_num_public = <Process as Program>::Aleo::num_public();
        let new_num_private = <Process as Program>::Aleo::num_private();
        let new_num_constraints = <Process as Program>::Aleo::num_constraints();

        // Check that the estimated counts is correct.
        assert!(count.is_satisfied(
            new_num_constants - old_num_constants,
            new_num_public - old_num_public,
            new_num_private - old_num_private,
            new_num_constraints - old_num_constraints
        ));

        let expected = Value::<Process>::from_str("false.private");

        match (&expected, &candidate[0]) {
            (Value::Literal(Literal::Boolean(expected)), Value::Literal(Literal::Boolean(candidate))) => {
                println!("{candidate}");
                assert!(expected.is_equal(candidate).eject_value());
            }
            _ => panic!("Failed to load output"),
        }
    }
}
