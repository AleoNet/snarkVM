// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<E: Environment, const RATE: usize> Hash for Poseidon<E, RATE> {
    type Input = Field<E>;
    type Output = Field<E>;

    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        self.hash_many(input, 1).swap_remove(0)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;

    use anyhow::Result;

    const DOMAIN: &str = "PoseidonCircuit0";
    const ITERATIONS: usize = 10;
    const RATE: usize = 4;

    fn check_hash(
        mode: Mode,
        num_inputs: usize,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
        rng: &mut TestRng,
    ) -> Result<()> {
        use console::Hash as H;

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let native_input = (0..num_inputs)
                .map(|_| console::Field::<<Circuit as Environment>::Network>::rand(rng))
                .collect::<Vec<_>>();
            let input = native_input.iter().map(|v| Field::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            let expected = native.hash(&native_input).expect("Failed to hash native input");

            // Compute the circuit hash.
            Circuit::scope(format!("Poseidon {mode} {i}"), || {
                let candidate = poseidon.hash(&input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
        Ok(())
    }

    #[test]
    fn test_hash_constant() -> Result<()> {
        let mut rng = TestRng::default();

        for num_inputs in 0..=RATE {
            check_hash(Mode::Constant, num_inputs, 1, 0, 0, 0, &mut rng)?;
        }
        Ok(())
    }

    #[test]
    fn test_hash_public() -> Result<()> {
        let mut rng = TestRng::default();

        check_hash(Mode::Public, 0, 1, 0, 0, 0, &mut rng)?;
        check_hash(Mode::Public, 1, 1, 0, 335, 335, &mut rng)?;
        check_hash(Mode::Public, 2, 1, 0, 340, 340, &mut rng)?;
        check_hash(Mode::Public, 3, 1, 0, 345, 345, &mut rng)?;
        check_hash(Mode::Public, 4, 1, 0, 350, 350, &mut rng)?;
        check_hash(Mode::Public, 5, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 6, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 7, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 8, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Public, 9, 1, 0, 1060, 1060, &mut rng)?;
        check_hash(Mode::Public, 10, 1, 0, 1060, 1060, &mut rng)
    }

    #[test]
    fn test_hash_private() -> Result<()> {
        let mut rng = TestRng::default();

        check_hash(Mode::Private, 0, 1, 0, 0, 0, &mut rng)?;
        check_hash(Mode::Private, 1, 1, 0, 335, 335, &mut rng)?;
        check_hash(Mode::Private, 2, 1, 0, 340, 340, &mut rng)?;
        check_hash(Mode::Private, 3, 1, 0, 345, 345, &mut rng)?;
        check_hash(Mode::Private, 4, 1, 0, 350, 350, &mut rng)?;
        check_hash(Mode::Private, 5, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 6, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 7, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 8, 1, 0, 705, 705, &mut rng)?;
        check_hash(Mode::Private, 9, 1, 0, 1060, 1060, &mut rng)?;
        check_hash(Mode::Private, 10, 1, 0, 1060, 1060, &mut rng)
    }

}

#[cfg(all(test, console))]
mod tests2 {
    use super::*;
    use snarkvm_circuit_types::environment::{Circuit,
                                             Environment,
                                             FormalCircuit,
                                             Transcribe};
    use snarkvm_circuit_types::Field;
    use snarkvm_console_types_field::{Field as ConsoleField, One, Zero};

    use anyhow::Result;

    use std::{
        str::FromStr,
    };

    const DOMAIN: &str = "Poseidon2";
    const RATE: usize = 2;

    #[test]
    // Note: it seems wrong that this outputs 0 constraints.

    // Circuit for poseidon rate 2 with zero inputs (empty input vector)
    fn psd_rate2_0() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let p = Poseidon2::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon2::hash(&p,&[]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd2 of 0 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }
    #[test]
    // Circuit for poseidon rate 2 with a single field element input
    fn psd_rate2_1() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let p = Poseidon2::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon2::hash(&p,&[a]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd2 of 1 input field ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }

    #[test]
    // Circuit for poseidon rate 2 with two field elements input
    fn psd_rate2_2() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let p = Poseidon2::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon2::hash(&p,&[a, b]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd2 of 2 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }

    #[test]
    // Circuit for poseidon rate 2 with three field elements input
    fn psd_rate2_3() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let c = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::from_str("2field").unwrap());
        let p = Poseidon2::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon2::hash(&p,&[a, b, c]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd2 of 3 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }
}

#[cfg(all(test, console))]
mod tests4 {
    use super::*;
    use snarkvm_circuit_types::environment::{Circuit,
                                             Environment,
                                             FormalCircuit,
                                             Transcribe};
    use snarkvm_circuit_types::Field;
    use snarkvm_console_types_field::{Field as ConsoleField, One, Zero};

    use anyhow::Result;

    use std::{
        str::FromStr,
    };

    const DOMAIN: &str = "Poseidon4";
    const RATE: usize = 4;

    #[test]
    // Note: it seems wrong that this outputs 0 constraints.

    // Circuit for poseidon rate 4 with zero inputs (empty input vector)
    fn psd_rate4_0() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(crate::poseidon::hash::tests4::DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let p = Poseidon4::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon4::hash(&p,&[]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd4 of 0 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }
    #[test]
    // Circuit for poseidon rate 4 with a single field element input
    fn psd_rate4_1() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(crate::poseidon::hash::tests4::DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let p = Poseidon4::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon4::hash(&p,&[a]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd4 of 1 input field ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }

    #[test]
    // Circuit for poseidon rate 4 with two field elements input
    fn psd_rate4_2() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(crate::poseidon::hash::tests4::DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let p = Poseidon4::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon4::hash(&p,&[a, b]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd4 of 2 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }

    #[test]
    // Circuit for poseidon rate 4 with three field elements input
    fn psd_rate4_3() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(crate::poseidon::hash::tests4::DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let c = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::from_str("2field").unwrap());
        let p = Poseidon4::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon4::hash(&p,&[a, b, c]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd4 of 3 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }

    #[test]
    // Circuit for poseidon rate 4 with four field elements input
    fn psd_rate4_4() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(crate::poseidon::hash::tests4::DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let c = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::from_str("2field").unwrap());
        let d = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::from_str("3field").unwrap());
        let p = Poseidon4::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon4::hash(&p,&[a, b, c, d]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd4 of 4 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }

    #[test]
    // Circuit for poseidon rate 4 with five field elements input
    fn psd_rate4_5() -> Result<()> {

        let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(crate::poseidon::hash::tests4::DOMAIN)?;
        //let poseidon = Poseidon::<Circuit, RATE>::constant(native.clone());

        let a = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::zero());
        let b = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::one());
        let c = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::from_str("2field").unwrap());
        let d = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::from_str("3field").unwrap());
        let e = Field::<FormalCircuit>::new(Mode::Private, ConsoleField::from_str("4field").unwrap());
        let p = Poseidon4::<FormalCircuit>::new(Mode::Private, native.clone());
        let _candidate = Poseidon4::hash(&p,&[a, b, c, d, e]);

        // print FormalCircuit to JSON in console
        let transcript = FormalCircuit::clear();
        let output = serde_json::to_string_pretty(&transcript).unwrap();
        println!("// psd4 of 5 input fields ({} constraints)",transcript.entries.len());
        println!("{}", output);
        Ok(())
    }

}
