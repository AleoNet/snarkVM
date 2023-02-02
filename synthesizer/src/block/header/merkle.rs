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

impl<N: Network> Header<N> {
    /// Returns the block header root.
    pub fn to_root(&self) -> Result<Field<N>> {
        Ok(*self.to_tree()?.root())
    }

    /// Returns the Merkle path for the Merkle tree of the block header.
    pub fn to_path(&self, leaf: &HeaderLeaf<N>) -> Result<HeaderPath<N>> {
        // Compute the Merkle path.
        self.to_tree()?.prove(leaf.index() as usize, &leaf.to_bits_le())
    }

    /// Returns the Merkle leaf for the given ID in the header.
    pub fn to_leaf(&self, id: &Field<N>) -> Result<HeaderLeaf<N>> {
        // If the ID is the previous state root, return the 0th leaf.
        if id == &self.previous_state_root {
            Ok(HeaderLeaf::<N>::new(0, self.previous_state_root))
        }
        // If the ID is the previous state root, return the 1st leaf.
        else if id == &self.transactions_root {
            Ok(HeaderLeaf::<N>::new(1, self.transactions_root))
        }
        // If the ID is the coinbase accumulator point, return the 2nd leaf.
        else if id == &self.coinbase_accumulator_point {
            Ok(HeaderLeaf::<N>::new(2, self.coinbase_accumulator_point))
        }
        // If the ID is the metadata hash, then return the 7th leaf.
        else if id == &self.metadata.to_hash()? {
            Ok(HeaderLeaf::<N>::new(7, *id))
        }
        // Otherwise, bail.
        else {
            bail!("Non-existent block header leaf ID: {id}")
        }
    }

    /// Returns an instance of the Merkle tree for the block header.
    pub fn to_tree(&self) -> Result<HeaderTree<N>> {
        // Determine the number of leaves.
        let num_leaves = usize::pow(2, HEADER_DEPTH as u32);

        // Construct the Merkle leaves.
        let mut leaves: Vec<Vec<bool>> = Vec::with_capacity(num_leaves);
        leaves.push(HeaderLeaf::<N>::new(0, self.previous_state_root).to_bits_le());
        leaves.push(HeaderLeaf::<N>::new(1, self.transactions_root).to_bits_le());
        leaves.push(HeaderLeaf::<N>::new(2, self.coinbase_accumulator_point).to_bits_le());
        for i in 3..7 {
            leaves.push(HeaderLeaf::<N>::new(i, Field::zero()).to_bits_le());
        }
        leaves.push(HeaderLeaf::<N>::new(7, self.metadata.to_hash()?).to_bits_le());

        // Ensure the correct number of leaves are allocated.
        ensure!(num_leaves == leaves.len(), "Incorrect number of leaves in the Merkle tree for the block header");

        // Compute the Merkle tree.
        N::merkle_tree_bhp::<HEADER_DEPTH>(&leaves)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;
    use snarkvm_utilities::TestRng;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1_000;

    fn check_path<N: Network>(header_path: HeaderPath<N>, root: Field<N>, leaf: &HeaderLeaf<N>) -> Result<()> {
        // Ensure that the path is valid for the corresponding root and leaf.
        assert!(N::verify_merkle_path_bhp(&header_path, &root, &leaf.to_bits_le()));

        // Check serialization.
        let expected_bytes = header_path.to_bytes_le()?;
        assert_eq!(header_path, HeaderPath::<N>::read_le(&expected_bytes[..])?);
        assert!(HeaderPath::<N>::read_le(&expected_bytes[1..]).is_err());
        Ok(())
    }

    #[test]
    fn test_merkle() -> Result<()> {
        let rng = &mut TestRng::default();

        for _ in 0..ITERATIONS {
            let coinbase_target = u64::rand(rng);
            let proof_target = rng.gen_range(0..coinbase_target);

            let header = Header::<CurrentNetwork>::from(
                Field::rand(rng),
                Field::rand(rng),
                Field::rand(rng),
                Metadata::new(
                    CurrentNetwork::ID,
                    u64::rand(rng),
                    u32::rand(rng),
                    coinbase_target,
                    proof_target,
                    u64::rand(rng),
                    rng.gen_range(0..i64::MAX),
                    rng.gen_range(0..i64::MAX),
                )?,
            )?;

            // Compute the header root.
            let root = header.to_root()?;

            // Check the 0th leaf.
            let leaf = header.to_leaf(&header.previous_state_root())?;
            assert_eq!(leaf.index(), 0);
            check_path(header.to_path(&leaf)?, root, &leaf)?;

            // Check the 1st leaf.
            let leaf = header.to_leaf(&header.transactions_root())?;
            assert_eq!(leaf.index(), 1);
            check_path(header.to_path(&leaf)?, root, &leaf)?;

            // Check the 2nd leaf.
            let leaf = header.to_leaf(&header.coinbase_accumulator_point())?;
            assert_eq!(leaf.index(), 2);
            check_path(header.to_path(&leaf)?, root, &leaf)?;

            // Check the 7th leaf.
            let leaf = header.to_leaf(&CurrentNetwork::hash_bhp512(&header.metadata().to_bits_le())?)?;
            assert_eq!(leaf.index(), 7);
            check_path(header.to_path(&leaf)?, root, &leaf)?;
        }

        Ok(())
    }
}
