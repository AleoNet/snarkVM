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

mod hash;
mod hash_uncompressed;

#[cfg(all(test, console))]
use snarkvm_circuit_types::environment::assert_scope;
use snarkvm_circuit_types::environment::Lookup;

use crate::{Hash, HashUncompressed};
use snarkvm_circuit_types::prelude::*;
use snarkvm_r1cs::LookupTable;

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
            let (x, y) = el.to_xy_coordinate();
            table.fill(*console::Field::<E::Network>::from_u16(i as u16), *x, *y);
        });
        E::add_lookup_table(table);

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
            // Initialize the native Pedersen hash.
            let native = console::Sinsemilla::<<Circuit as Environment>::Network, NUM_WINDOWS>::setup(MESSAGE);
            let native_2 = console::Sinsemilla::<<Circuit as Environment>::Network, NUM_WINDOWS>::setup(MESSAGE);

            Circuit::scope("Sinsemilla::setup", || {
                // Perform the setup operation.
                let circuit = Sinsemilla::<Circuit, NUM_WINDOWS>::new(Mode::Constant, native_2);
                assert_scope!(num_constants, num_public, num_private, num_constraints);

                // Check for equivalency of the Q.
                assert_eq!(native.q(), circuit.q.eject_value());

                // Check for equality of the lookup table.
                // native.p_lookups().iter().zip_eq(circuit.p_lookups.iter()).for_each(|(expected, candidate)| {
                //     assert_eq!(expected.to_affine(), candidate.eject_value());
                // });
            });
        }
    }

    #[test]
    fn test_setup_constant() {
        // Set the number of windows, and modulate the window size.
        check_setup::<10>(4, 0, 0, 0);
    }
}
