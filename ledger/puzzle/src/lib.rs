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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]
#![warn(clippy::cast_possible_truncation)]

mod solution;
pub use solution::*;

mod solution_id;
pub use solution_id::*;

mod solutions;
pub use solutions::*;

use console::{
    account::Address,
    algorithms::Sha3_256,
    collections::kary_merkle_tree::KaryMerkleTree,
    prelude::{
        anyhow,
        bail,
        cfg_into_iter,
        cfg_iter,
        cfg_keys,
        cfg_values,
        ensure,
        has_duplicates,
        FromBits,
        Network,
        Result,
    },
    types::U64,
};

use aleo_std::prelude::*;
use core::num::NonZeroUsize;
use indexmap::IndexMap;
use lru::LruCache;
use parking_lot::RwLock;
use rand::SeedableRng;
use rand_chacha::ChaChaRng;
use std::sync::Arc;

#[cfg(not(feature = "serial"))]
use rayon::prelude::*;

/// The arity of the Merkle tree.
const ARITY: u8 = 8;

/// The Merkle tree for the puzzle.
type MerkleTree = KaryMerkleTree<Sha3_256, Sha3_256, 8, { ARITY }>;

/// The puzzle trait.
pub trait PuzzleTrait<N: Network>: Send + Sync {
    /// Initializes a new instance of the puzzle.
    fn new() -> Self
    where
        Self: Sized;

    /// Returns the leaves for the puzzle, given the epoch hash and seeded RNG.
    fn to_leaves(&self, epoch_hash: N::BlockHash, rng: &mut ChaChaRng) -> Result<Vec<Vec<bool>>>;

    /// Returns the batches of leaves for the puzzle, given the epoch hash and seeded RNGs.
    fn to_all_leaves(&self, epoch_hash: N::BlockHash, rngs: Vec<ChaChaRng>) -> Result<Vec<Vec<Vec<bool>>>>;
}

#[derive(Clone)]
pub struct Puzzle<N: Network> {
    /// The core puzzle.
    inner: Arc<dyn PuzzleTrait<N>>,
    /// The LRU cache of solution IDs to proof targets.
    proof_target_cache: Arc<RwLock<LruCache<SolutionID<N>, u64>>>,
}

impl<N: Network> Puzzle<N> {
    /// Initializes a new puzzle instance.
    pub fn new<P: PuzzleTrait<N> + 'static>() -> Self {
        Self {
            inner: Arc::new(P::new()),
            proof_target_cache: Arc::new(RwLock::new(LruCache::new(NonZeroUsize::new(1 << 10).unwrap()))),
        }
    }

    /// Returns the Merkle leaves for the puzzle, given the solution.
    pub fn get_leaves(&self, solution: &Solution<N>) -> Result<Vec<Vec<bool>>> {
        // Initialize a seeded random number generator.
        let mut rng = ChaChaRng::seed_from_u64(*solution.id());
        // Output the leaves.
        self.inner.to_leaves(solution.epoch_hash(), &mut rng)
    }

    /// Returns each of the Merkle leaves for the puzzle, given the solutions.
    pub fn get_all_leaves(&self, solutions: &PuzzleSolutions<N>) -> Result<Vec<Vec<Vec<bool>>>> {
        // Ensure all of the solutions are for the same epoch.
        ensure!(
            cfg_values!(solutions).all(|solution| solution.epoch_hash() == solutions[0].epoch_hash()),
            "The solutions are for different epochs"
        );
        // Construct the RNGs.
        let rngs = cfg_keys!(solutions).map(|solution_id| ChaChaRng::seed_from_u64(**solution_id)).collect::<Vec<_>>();
        // Output the leaves.
        self.inner.to_all_leaves(solutions[0].epoch_hash(), rngs)
    }

    /// Returns the proof target given the solution.
    pub fn get_proof_target(&self, solution: &Solution<N>) -> Result<u64> {
        // If the proof target is in the cache, then return it.
        if let Some(proof_target) = self.proof_target_cache.write().get(&solution.id()) {
            return Ok(*proof_target);
        }

        // Construct the leaves of the Merkle tree.
        let leaves = self.get_leaves(solution)?;
        // Construct the Merkle tree.
        let merkle_tree = MerkleTree::new(&Sha3_256::default(), &Sha3_256::default(), &leaves)?;
        // Retrieve the Merkle tree root.
        let root = merkle_tree.root();
        // Truncate to a u64.
        let proof_target = match *U64::<N>::from_bits_be(&root[0..64])? {
            0 => u64::MAX,
            value => u64::MAX / value,
        };

        // Insert the proof target into the cache.
        self.proof_target_cache.write().put(solution.id(), proof_target);
        // Return the proof target.
        Ok(proof_target)
    }

    /// Returns the proof targets given the solutions.
    pub fn get_proof_targets(&self, solutions: &PuzzleSolutions<N>) -> Result<Vec<u64>> {
        // Initialize the list of proof targets.
        let mut targets = vec![0u64; solutions.len()];

        // Initialize a list of solutions that need to be computed for the proof target.
        let mut to_compute = Vec::new();
        // Iterate over the solutions.
        for (i, (id, solution)) in solutions.iter().enumerate() {
            // Check if the proof target is in the cache.
            match self.proof_target_cache.write().get(id) {
                // If the proof target is in the cache, then store it.
                Some(proof_target) => targets[i] = *proof_target,
                // Otherwise, add it to the list of solutions that need to be computed.
                None => to_compute.push((i, id, *solution)),
            }
        }

        if !to_compute.is_empty() {
            // Construct the solutions object for those that need to be computed.
            let solutions_subset = PuzzleSolutions::new(to_compute.iter().map(|(_, _, solution)| *solution).collect())?;
            // Construct the leaves of the Merkle tree.
            let leaves = self.get_all_leaves(&solutions_subset)?;
            // Construct the Merkle roots and truncate them to a u64.
            let targets_subset = cfg_iter!(leaves)
                .zip(cfg_keys!(solutions_subset))
                .map(|(leaves, solution_id)| {
                    // Construct the Merkle tree.
                    let merkle_tree = MerkleTree::new(&Sha3_256::default(), &Sha3_256::default(), leaves)?;
                    // Retrieve the Merkle tree root.
                    let root = merkle_tree.root();
                    // Truncate to a u64.
                    let proof_target = match *U64::<N>::from_bits_be(&root[0..64])? {
                        0 => u64::MAX,
                        value => u64::MAX / value,
                    };
                    // Insert the proof target into the cache.
                    self.proof_target_cache.write().put(*solution_id, proof_target);
                    // Return the proof target.
                    Ok((solution_id, proof_target))
                })
                .collect::<Result<IndexMap<_, _>>>()?;

            // Recombine the proof targets.
            for (i, id, _) in to_compute.iter() {
                targets[*i] = targets_subset[id];
            }
        }

        // Return the proof targets.
        Ok(targets)
    }

    /// Returns the combined proof target of the solutions.
    pub fn get_combined_proof_target(&self, solutions: &PuzzleSolutions<N>) -> Result<u128> {
        self.get_proof_targets(solutions)?.into_iter().try_fold(0u128, |combined, proof_target| {
            combined.checked_add(proof_target as u128).ok_or_else(|| anyhow!("Combined proof target overflowed"))
        })
    }

    /// Returns a solution to the puzzle.
    pub fn prove(
        &self,
        epoch_hash: N::BlockHash,
        address: Address<N>,
        counter: u64,
        minimum_proof_target: Option<u64>,
    ) -> Result<Solution<N>> {
        // Construct the solution.
        let solution = Solution::new(epoch_hash, address, counter)?;
        // Compute the proof target.
        let proof_target = self.get_proof_target(&solution)?;
        // Check that the minimum proof target is met.
        if let Some(minimum_proof_target) = minimum_proof_target {
            if proof_target < minimum_proof_target {
                bail!("Solution was below the minimum proof target ({proof_target} < {minimum_proof_target})")
            }
        }
        // Return the solution.
        Ok(solution)
    }

    /// Returns `Ok(())` if the solution is valid.
    pub fn check_solution(
        &self,
        solution: &Solution<N>,
        expected_epoch_hash: N::BlockHash,
        expected_proof_target: u64,
    ) -> Result<()> {
        // Ensure the epoch hash matches.
        if solution.epoch_hash() != expected_epoch_hash {
            bail!(
                "Solution does not match the expected epoch hash (found '{}', expected '{expected_epoch_hash}')",
                solution.epoch_hash()
            )
        }
        // Ensure the solution is greater than or equal to the expected proof target.
        let proof_target = self.get_proof_target(solution)?;
        if proof_target < expected_proof_target {
            bail!("Solution does not meet the proof target requirement ({proof_target} < {expected_proof_target})")
        }
        Ok(())
    }

    /// Returns `Ok(())` if the solutions are valid.
    pub fn check_solutions(
        &self,
        solutions: &PuzzleSolutions<N>,
        expected_epoch_hash: N::BlockHash,
        expected_proof_target: u64,
    ) -> Result<()> {
        let timer = timer!("Puzzle::verify");

        // Ensure the solutions are not empty.
        ensure!(!solutions.is_empty(), "The solutions are empty");
        // Ensure the number of solutions does not exceed `MAX_SOLUTIONS`.
        if solutions.len() > N::MAX_SOLUTIONS {
            bail!("Exceed the maximum number of solutions ({} > {})", solutions.len(), N::MAX_SOLUTIONS)
        }
        // Ensure the solution IDs are unique.
        if has_duplicates(solutions.solution_ids()) {
            bail!("The solutions contain duplicate solution IDs");
        }
        lap!(timer, "Perform initial checks");

        // Ensure the epoch hash matches.
        cfg_iter!(solutions).try_for_each(|(solution_id, solution)| {
            if solution.epoch_hash() != expected_epoch_hash {
                bail!("Solution '{solution_id}' did not match the expected epoch hash (found '{}', expected '{expected_epoch_hash}')", solution.epoch_hash())
            }
            Ok(())
        })?;
        lap!(timer, "Verify each epoch hash matches");

        // Ensure the solutions meet the proof target requirement.
        cfg_into_iter!(self.get_proof_targets(solutions)?).enumerate().try_for_each(|(i, proof_target)| {
            if proof_target < expected_proof_target {
                bail!(
                    "Solution '{:?}' did not meet the proof target requirement ({proof_target} < {expected_proof_target})",
                    solutions.get_index(i).map(|(id, _)| id)
                )
            }
            Ok(())
        })?;
        finish!(timer, "Verify each solution");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::{
        account::{Address, PrivateKey},
        network::Network,
        prelude::{FromBytes, TestRng, ToBits as TBits, ToBytes, Uniform},
        types::Field,
    };

    use anyhow::Result;
    use core::marker::PhantomData;
    use rand::{CryptoRng, Rng, RngCore, SeedableRng};
    use rand_chacha::ChaChaRng;

    type CurrentNetwork = console::network::MainnetV0;

    const ITERATIONS: u64 = 100;

    pub struct SimplePuzzle<N: Network>(PhantomData<N>);

    impl<N: Network> PuzzleTrait<N> for SimplePuzzle<N> {
        /// Initializes a new instance of the puzzle.
        fn new() -> Self {
            Self(PhantomData)
        }

        /// Returns the leaves for the puzzle, given the epoch hash and seeded RNG.
        fn to_leaves(&self, epoch_hash: N::BlockHash, rng: &mut ChaChaRng) -> Result<Vec<Vec<bool>>> {
            // Sample a random number of leaves.
            let num_leaves = self.num_leaves(epoch_hash)?;
            // Sample random field elements for each of the leaves, and convert them to bits.
            let leaves = (0..num_leaves).map(|_| Field::<N>::rand(rng).to_bits_le()).collect::<Vec<_>>();
            // Return the leaves.
            Ok(leaves)
        }

        /// Returns the batches of leaves for the puzzle, given the epoch hash and seeded RNGs.
        fn to_all_leaves(&self, epoch_hash: N::BlockHash, rngs: Vec<ChaChaRng>) -> Result<Vec<Vec<Vec<bool>>>> {
            // Sample a random number of leaves.
            let num_leaves = self.num_leaves(epoch_hash)?;
            // Initialize the list of leaves.
            let mut leaves = Vec::with_capacity(rngs.len());
            // Construct the epoch inputs.
            for mut rng in rngs {
                // Sample random field elements for each of the leaves, and convert them to bits.
                leaves.push((0..num_leaves).map(|_| Field::<N>::rand(&mut rng).to_bits_le()).collect::<Vec<_>>());
            }
            // Return the leaves.
            Ok(leaves)
        }
    }

    impl<N: Network> SimplePuzzle<N> {
        /// Returns the number of leaves given the epoch hash.
        pub fn num_leaves(&self, epoch_hash: N::BlockHash) -> Result<usize> {
            const MIN_NUMBER_OF_LEAVES: usize = 100;
            const MAX_NUMBER_OF_LEAVES: usize = 200;

            // Prepare the seed.
            let seed = u64::from_bytes_le(&epoch_hash.to_bytes_le()?[0..8])?;
            // Seed a random number generator from the epoch hash.
            let mut epoch_rng = ChaChaRng::seed_from_u64(seed);
            // Sample a random number of leaves.
            Ok(epoch_rng.gen_range(MIN_NUMBER_OF_LEAVES..MAX_NUMBER_OF_LEAVES))
        }
    }

    /// Samples a new puzzle.
    fn sample_puzzle() -> Puzzle<CurrentNetwork> {
        Puzzle::<CurrentNetwork>::new::<SimplePuzzle<CurrentNetwork>>()
    }

    #[test]
    fn test_puzzle() {
        let mut rng = TestRng::default();

        // Initialize a new puzzle.
        let puzzle = sample_puzzle();

        // Initialize an epoch hash.
        let epoch_hash = rng.gen();

        for batch_size in 1..=CurrentNetwork::MAX_SOLUTIONS {
            // Initialize the solutions.
            let solutions = (0..batch_size)
                .map(|_| puzzle.prove(epoch_hash, rng.gen(), rng.gen(), None).unwrap())
                .collect::<Vec<_>>();
            let solutions = PuzzleSolutions::new(solutions).unwrap();

            // Ensure the solutions are valid.
            assert!(puzzle.check_solutions(&solutions, epoch_hash, 0u64).is_ok());

            // Ensure the solutions are invalid.
            let bad_epoch_hash = rng.gen();
            assert!(puzzle.check_solutions(&solutions, bad_epoch_hash, 0u64).is_err());
        }
    }

    #[test]
    fn test_prove_with_minimum_proof_target() {
        let mut rng = TestRng::default();

        // Initialize a new puzzle.
        let puzzle = sample_puzzle();

        // Initialize an epoch hash.
        let epoch_hash = rng.gen();

        for _ in 0..ITERATIONS {
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng).unwrap();
            let address = Address::try_from(private_key).unwrap();
            let counter = u64::rand(&mut rng);

            let solution = puzzle.prove(epoch_hash, address, counter, None).unwrap();
            let proof_target = puzzle.get_proof_target(&solution).unwrap();

            // Assert that the operation will pass if the minimum target is low enough.
            assert!(puzzle.prove(epoch_hash, address, counter, Some(proof_target)).is_ok());

            // Assert that the operation will fail if the minimum target is too high.
            assert!(puzzle.prove(epoch_hash, address, counter, Some(proof_target.saturating_add(1))).is_err());

            let solutions = PuzzleSolutions::new(vec![solution]).unwrap();

            // Ensure the solution is valid.
            assert!(puzzle.check_solutions(&solutions, epoch_hash, proof_target).is_ok());

            // Ensure the solution is invalid.
            assert!(puzzle.check_solutions(&solutions, epoch_hash, proof_target.saturating_add(1)).is_err());
        }
    }

    #[test]
    fn test_prove_with_no_minimum_proof_target() {
        let mut rng = rand::thread_rng();

        // Initialize a new puzzle.
        let puzzle = sample_puzzle();

        // Initialize an epoch hash.
        let epoch_hash = rng.gen();

        // Generate inputs.
        let private_key = PrivateKey::<CurrentNetwork>::new(&mut rng).unwrap();
        let address = Address::try_from(private_key).unwrap();

        // Generate a solution.
        let solution = puzzle.prove(epoch_hash, address, rng.gen(), None).unwrap();
        assert!(puzzle.check_solution(&solution, epoch_hash, 0u64).is_ok());

        let solutions = PuzzleSolutions::new(vec![solution]).unwrap();
        assert!(puzzle.check_solutions(&solutions, epoch_hash, 0u64).is_ok());
    }

    #[test]
    fn test_check_solutions_with_duplicate_nonces() {
        let mut rng = TestRng::default();

        // Initialize a new puzzle.
        let puzzle = sample_puzzle();

        // Initialize an epoch hash.
        let epoch_hash = rng.gen();
        // Initialize an address.
        let address = rng.gen();
        // Initialize a counter.
        let counter = rng.gen();

        for batch_size in 1..=CurrentNetwork::MAX_SOLUTIONS {
            // Initialize the solutions.
            let solutions =
                (0..batch_size).map(|_| puzzle.prove(epoch_hash, address, counter, None).unwrap()).collect::<Vec<_>>();
            // Ensure the solutions are invalid, if the batch size is greater than 1.
            let solutions = match batch_size {
                1 => PuzzleSolutions::new(solutions).unwrap(),
                _ => {
                    assert!(PuzzleSolutions::new(solutions).is_err());
                    continue;
                }
            };
            match batch_size {
                1 => assert!(puzzle.check_solutions(&solutions, epoch_hash, 0u64).is_ok()),
                _ => unreachable!("There are duplicates that should not reach this point in the test"),
            }
        }
    }

    #[test]
    fn test_get_proof_targets_without_cache() {
        let mut rng = TestRng::default();

        // Initialize an epoch hash.
        let epoch_hash = rng.gen();

        for batch_size in 1..=CurrentNetwork::MAX_SOLUTIONS {
            // Initialize a new puzzle.
            let puzzle = sample_puzzle();
            // Initialize the solutions.
            let solutions = (0..batch_size)
                .map(|_| puzzle.prove(epoch_hash, rng.gen(), rng.gen(), None).unwrap())
                .collect::<Vec<_>>();
            let solutions = PuzzleSolutions::new(solutions).unwrap();

            // Reinitialize the puzzle to *clear the cache*.
            let puzzle = sample_puzzle();

            // Compute the proof targets.
            let proof_targets = puzzle.get_proof_targets(&solutions).unwrap();

            // Ensure the proof targets are correct.
            for ((_, solution), proof_target) in solutions.iter().zip(proof_targets) {
                assert_eq!(puzzle.get_proof_target(solution).unwrap(), proof_target);
            }
        }
    }

    #[test]
    fn test_get_proof_targets_with_partial_cache() {
        let mut rng = TestRng::default();

        // Initialize an epoch hash.
        let epoch_hash = rng.gen();

        for batch_size in 1..=CurrentNetwork::MAX_SOLUTIONS {
            // Initialize a new puzzle.
            let puzzle = sample_puzzle();
            // Initialize the solutions.
            let solutions = (0..batch_size)
                .map(|_| puzzle.prove(epoch_hash, rng.gen(), rng.gen(), None).unwrap())
                .collect::<Vec<_>>();
            let solutions = PuzzleSolutions::new(solutions).unwrap();

            // Reinitialize the puzzle to *clear the cache*.
            let puzzle = sample_puzzle();

            // Partially fill the cache.
            for solution in solutions.values() {
                // Flip a coin.
                if rng.gen::<bool>() {
                    // This operation will fill the cache.
                    puzzle.get_proof_target(solution).unwrap();
                }
            }

            // Compute the proof targets.
            let proof_targets = puzzle.get_proof_targets(&solutions).unwrap();

            // Ensure the proof targets are correct.
            for ((_, solution), proof_target) in solutions.iter().zip(proof_targets) {
                assert_eq!(puzzle.get_proof_target(solution).unwrap(), proof_target);
            }
        }
    }

    /// Use `cargo test profiler --features timer` to run this test.
    #[ignore]
    #[test]
    fn test_profiler() -> Result<()> {
        fn sample_address_and_counter(rng: &mut (impl CryptoRng + RngCore)) -> (Address<CurrentNetwork>, u64) {
            let private_key = PrivateKey::new(rng).unwrap();
            let address = Address::try_from(private_key).unwrap();
            let counter = rng.next_u64();
            (address, counter)
        }

        let mut rng = rand::thread_rng();

        // Initialize a new puzzle.
        let puzzle = sample_puzzle();

        // Initialize an epoch hash.
        let epoch_hash = rng.gen();

        for batch_size in [1, 2, <CurrentNetwork as Network>::MAX_SOLUTIONS] {
            // Generate the solutions.
            let solutions = (0..batch_size)
                .map(|_| {
                    let (address, counter) = sample_address_and_counter(&mut rng);
                    puzzle.prove(epoch_hash, address, counter, None).unwrap()
                })
                .collect::<Vec<_>>();
            // Construct the solutions.
            let solutions = PuzzleSolutions::new(solutions).unwrap();
            // Verify the solutions.
            puzzle.check_solutions(&solutions, epoch_hash, 0u64).unwrap();
        }

        bail!("\n\nRemember to #[ignore] this test!\n\n")
    }
}
