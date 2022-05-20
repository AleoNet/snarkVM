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

mod hash;
mod hash_uncompressed;

#[cfg(all(test, console))]
use snarkvm_circuit_types::environment::assert_scope;
use snarkvm_circuit_types::environment::Lookup;

use crate::{Hash, HashUncompressed};
use snarkvm_algorithms::r1cs::LookupTable;
use snarkvm_circuit_types::prelude::*;

/// Sinsemilla is a collision-resistant hash function that takes a fixed-length input.
/// The Sinsemilla hash function does *not* behave like a random oracle, see Poseidon for one.
pub struct Sinsemilla<E: Lookup + Environment, const NUM_WINDOWS: u8> {
    q: Group<E>,
}

#[cfg(console)]
impl<E: Lookup + Environment, const NUM_WINDOWS: u8> Inject for Sinsemilla<E, NUM_WINDOWS> {
    type Primitive = console::Sinsemilla<E::Network, NUM_WINDOWS>;

    /// Initializes a new instance of Sinsemilla with the given setup message.
    fn new(_mode: Mode, sinsemilla: Self::Primitive) -> Self {
        // Push the lookup table into the constraint system.
        let mut table = LookupTable::default();
        sinsemilla.p_lookups().iter().enumerate().for_each(|(i, el)| {
            let x = el.to_x_coordinate();
            let y = el.to_y_coordinate();
            table.fill(*console::Field::<E::Network>::from_u16(i as u16), *x, *y);
        });
        <E as Lookup>::add_lookup_table(table);

        Self { q: Group::constant(sinsemilla.q()) }
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "SinsemillaCircuit0";

    fn check_setup<const NUM_WINDOWS: u8>(num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        for _ in 0..ITERATIONS {
            // Initialize the native Sinsemilla hash.
            let native = console::Sinsemilla::<<Circuit as Environment>::Network, NUM_WINDOWS>::setup(MESSAGE);
            let q = native.q();

            Circuit::scope("Sinsemilla::setup", || {
                // Perform the setup operation.
                let circuit = Sinsemilla::<Circuit, NUM_WINDOWS>::new(Mode::Constant, native);
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Check for equivalency of the Q.
                assert_eq!(q, circuit.q.eject_value());
            });
        }
    }

    #[test]
    fn test_setup_constant() {
        check_setup::<10>(10, 0, 0, 0);
    }
}
