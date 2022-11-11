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
use console::{account::*, network::Testnet3};
use snarkvm_utilities::Uniform;

use rand::RngCore;

const ITERATIONS: u64 = 100;

#[test]
fn test_coinbase_puzzle() {
    let mut rng = TestRng::default();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for log_degree in 5..10 {
        let degree = (1 << log_degree) - 1;
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
        let epoch_challenge = EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap();

        for batch_size in 1..10 {
            let solutions = (0..batch_size)
                .map(|_| {
                    let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
                    let address = Address::try_from(private_key).unwrap();
                    let nonce = u64::rand(&mut rng);
                    puzzle.prove(&epoch_challenge, address, nonce, None).unwrap()
                })
                .collect::<Vec<_>>();
            let full_solution = puzzle.accumulate_unchecked(&epoch_challenge, &solutions).unwrap();
            assert!(puzzle.verify(&full_solution, &epoch_challenge, 0u64, 0u64).unwrap());

            let bad_epoch_challenge = EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap();
            assert!(!puzzle.verify(&full_solution, &bad_epoch_challenge, 0u64, 0u64).unwrap());
        }
    }
}

#[test]
fn test_prover_solution_minimum_target() {
    let mut rng = TestRng::default();

    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    for log_degree in 5..10 {
        let degree = (1 << log_degree) - 1;
        let config = PuzzleConfig { degree };
        let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, config).unwrap();
        let epoch_challenge = EpochChallenge::new(rng.next_u32(), Default::default(), degree).unwrap();

        for _ in 0..ITERATIONS {
            let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
            let address = Address::try_from(private_key).unwrap();
            let nonce = u64::rand(&mut rng);

            // Assert that the puzzle can always be solved with a minimum target of 0.
            assert!(puzzle.prove(&epoch_challenge, address, nonce, Some(0)).is_ok());

            // Assert that the puzzle can't be solved with a maximum target of u64::MAX.
            // Unless the target is exactly u64::MAX.
            let proof_result = puzzle.prove(&epoch_challenge, address, nonce, Some(u64::MAX));
            if let Ok(proof) = proof_result {
                assert_eq!(proof.to_target().unwrap(), u64::MAX);
            } else {
                assert!(proof_result.is_err());
            }
        }
    }
}

#[test]
fn test_edge_case_for_degree() {
    let mut rng = rand::thread_rng();

    // Generate srs.
    let max_degree = 1 << 15;
    let max_config = PuzzleConfig { degree: max_degree };
    let srs = CoinbasePuzzle::<Testnet3>::setup(max_config).unwrap();

    // Generate PK and VK.
    let degree = (1 << 13) - 1; // IF YOU ADD `- 1` THIS WILL PASS
    let puzzle = CoinbasePuzzle::<Testnet3>::trim(&srs, PuzzleConfig { degree }).unwrap();

    // Generate proof inputs
    let private_key = PrivateKey::<Testnet3>::new(&mut rng).unwrap();
    let address = Address::try_from(private_key).unwrap();
    let epoch_challenge = EpochChallenge::new(rng.gen(), Default::default(), degree).unwrap();

    // Generate a prover solution.
    let prover_solution = puzzle.prove(&epoch_challenge, address, rng.gen(), None).unwrap();
    let coinbase_solution = puzzle.accumulate_unchecked(&epoch_challenge, &[prover_solution]).unwrap();
    assert!(puzzle.verify(&coinbase_solution, &epoch_challenge, 0u64, 0u64).unwrap());
}
