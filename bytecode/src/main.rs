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

use snarkvm_bytecode::{Function, Memory, Stack};
use snarkvm_circuits::prelude::*;

pub struct HelloWorld;

impl HelloWorld {
    /// Initializes a new instance of `HelloWorld` with the given inputs.
    pub fn run<M: Memory>(inputs: [Literal<M::Environment>; 2]) -> Vec<Literal<M::Environment>> {
        Function::<M>::from_str(
            r"
function main:
    input r0 field.public;
    input r1 field.private;
    add r2 r0 r1;
    output r2 field.private;
",
        )
        .evaluate(&inputs)
    }
}

fn main() {
    let first = Literal::from_str("1field.public");
    let second = Literal::from_str("1field.private");

    let expected = Literal::from_str("2field.private");
    let candidate = HelloWorld::run::<Stack<Circuit>>([first, second]);

    match (&expected, &candidate[0]) {
        (Literal::Field(expected), Literal::Field(candidate)) => {
            println!("{candidate}");
            assert!(expected.is_equal(candidate).eject_value());
        }
        _ => panic!("Failed to load output"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_utilities::{FromBytes, ToBytes};

    #[test]
    fn test_hello_world() {
        let first = Literal::from_str("1field.public");
        let second = Literal::from_str("1field.private");

        let expected = Literal::from_str("2field.private");
        let candidate = HelloWorld::run::<Stack<Circuit>>([first, second]);

        match (&expected, &candidate[0]) {
            (Literal::Field(expected), Literal::Field(candidate)) => {
                assert!(expected.is_equal(candidate).eject_value())
            }
            _ => panic!("Failed to load output"),
        }
    }

    #[test]
    fn test_to_and_from_bytes() {
        type M = Stack<Circuit>;
        let function_string = r"
function main:
    input r0 field.public;
    input r1 field.private;
    add r2 r0 r1;
    add r3 r0 r1;
    add r4 r0 r1;
    add r5 r0 r1;
    add r6 r0 r1;
    add r7 r0 r1;
    add r8 r0 r1;
    add r9 r0 r1;
    add r10 r0 r1;
    add r11 r0 r1;
    output r2 field.private;
";
        let function_from_string = Function::<M>::from_str(function_string);
        let bytes = function_from_string.to_bytes_le().unwrap();

        println!("String size: {:?}, Bytecode size: {:?}", function_string.as_bytes().len(), bytes.len());

        Function::<M>::from_bytes_le(&bytes).unwrap();
    }

    #[test]
    fn test_marlin() {
        pub struct HelloWorld;

        impl HelloWorld {
            /// Initializes a new instance of `HelloWorld` with the given inputs.
            pub fn run<M: Memory>(inputs: &[Literal<M::Environment>]) -> Vec<Literal<M::Environment>> {
                Function::<M>::from_str(
                    r"
function main:
    input r0 u8.public;
    input r1 u8.private;
    add r2 r0 r1;
    output r2 u8.private;
",
                )
                .evaluate(inputs)
            }
        }

        // Initialize the inputs.
        let input = [Literal::from_str("1u8.public"), Literal::from_str("1u8.private")];

        // Run the function.
        let _output = HelloWorld::run::<Stack<Circuit>>(&input);

        // Marlin setup, prove, and verify.
        {
            use snarkvm_algorithms::{
                crypto_hash::poseidon::PoseidonSponge,
                polycommit::sonic_pc::SonicKZG10,
                snark::marlin::{
                    ahp::AHPForR1CS,
                    fiat_shamir::FiatShamirAlgebraicSpongeRng,
                    MarlinHidingMode,
                    MarlinSNARK,
                },
            };
            use snarkvm_curves::bls12_377::{Bls12_377, Fq, Fr};
            use snarkvm_utilities::rand::test_rng;

            type MultiPC = SonicKZG10<Bls12_377>;
            type FS = FiatShamirAlgebraicSpongeRng<Fr, Fq, PoseidonSponge<Fq, 6, 1>>;
            type MarlinInst = MarlinSNARK<Fr, Fq, MultiPC, FS, MarlinHidingMode, Vec<Fr>>;

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
