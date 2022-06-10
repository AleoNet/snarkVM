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

use super::*;
use snarkvm_circuit_algorithms::{Hash, Poseidon, BHP};

/// A trait for a Merkle leaf hash function.
pub trait LeafHash<E: Environment> {
    type Leaf;
    type Hash: FieldTrait;

    /// Returns the hash of the given leaf node.
    fn hash_leaf(&self, leaf: &Self::Leaf) -> Self::Hash;
}

impl<E: Environment, const NUM_WINDOWS: u8, const WINDOW_SIZE: u8> LeafHash<E> for BHP<E, NUM_WINDOWS, WINDOW_SIZE> {
    type Hash = Field<E>;
    type Leaf = Vec<Boolean<E>>;

    /// Returns the hash of the given leaf node.
    fn hash_leaf(&self, leaf: &Self::Leaf) -> Self::Hash {
        // Prepend the leaf with a `false` bit.
        let mut input = vec![Boolean::constant(false)];
        input.extend_from_slice(leaf);
        // Hash the input.
        Hash::hash(self, &input)
    }
}

impl<E: Environment, const RATE: usize> LeafHash<E> for Poseidon<E, RATE> {
    type Hash = Field<E>;
    type Leaf = Vec<Field<E>>;

    /// Returns the hash of the given leaf node.
    fn hash_leaf(&self, leaf: &Self::Leaf) -> Self::Hash {
        // Prepend the leaf with a `0field` element.
        let mut input = vec![Self::Hash::zero()];
        input.extend_from_slice(leaf);
        // Hash the input.
        Hash::hash(self, &input)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_algorithms::{Poseidon4, BHP1024};
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_utilities::{test_rng, Uniform};

    use anyhow::Result;

    const ITERATIONS: u64 = 10;
    const DOMAIN: &str = "MerkleTreeCircuit0";

    macro_rules! check_hash_leaf {
        ($hash:ident, $mode:ident, $num_inputs:expr, ($num_constants:expr, $num_public:expr, $num_private:expr, $num_constraints:expr)) => {{
            // Initialize the hash.
            let native = snarkvm_console_algorithms::$hash::<<Circuit as Environment>::Network>::setup(DOMAIN)?;
            let circuit = $hash::<Circuit>::constant(native.clone());

            for i in 0..ITERATIONS {
                // Sample a random input.
                let input = (0..$num_inputs).map(|_| Uniform::rand(&mut test_rng())).collect::<Vec<_>>();

                // Compute the expected hash.
                let expected = console::merkle_tree::LeafHash::hash_leaf(&native, &input)?;

                // Prepare the circuit input.
                let circuit_input: Vec<_> = Inject::new(Mode::$mode, input);

                Circuit::scope(format!("LeafHash {i}"), || {
                    // Perform the hash operation.
                    let candidate = circuit.hash_leaf(&circuit_input);
                    assert_scope!($num_constants, $num_public, $num_private, $num_constraints);
                    assert_eq!(expected, candidate.eject_value());
                });
                Circuit::reset();
            }
            Ok::<_, anyhow::Error>(())
        }};
    }

    #[test]
    fn test_hash_leaf_bhp1024_constant() -> Result<()> {
        check_hash_leaf!(BHP1024, Constant, 1024, (1807, 0, 0, 0))
    }

    #[test]
    fn test_hash_leaf_bhp1024_public() -> Result<()> {
        check_hash_leaf!(BHP1024, Public, 1024, (429, 0, 1758, 1758))
    }

    #[test]
    fn test_hash_leaf_bhp1024_private() -> Result<()> {
        check_hash_leaf!(BHP1024, Private, 1024, (429, 0, 1758, 1758))
    }

    #[test]
    fn test_hash_leaf_poseidon4_constant() -> Result<()> {
        check_hash_leaf!(Poseidon4, Constant, 4, (1, 0, 0, 0))
    }

    #[test]
    fn test_hash_leaf_poseidon4_public() -> Result<()> {
        check_hash_leaf!(Poseidon4, Public, 4, (1, 0, 700, 700))
    }

    #[test]
    fn test_hash_leaf_poseidon4_private() -> Result<()> {
        check_hash_leaf!(Poseidon4, Private, 4, (1, 0, 700, 700))
    }
}
