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

use rand::RngCore;
use snarkvm_curves::bls12_377::Bls12_377;
use snarkvm_utilities::Uniform;

use super::*;

#[test]
fn test_coinbase_puzzle() {
    let max_degree = 1 << 15;
    let mut rng = rand::thread_rng();

    let srs = CoinbasePuzzle::<Bls12_377>::setup(max_degree, &mut rng);
    for log_degree in 5..10 {
        let degree = (1 << log_degree) - 1;
        let (pk, vk) = CoinbasePuzzle::trim(&srs, degree);
        let epoch_info = EpochInfo { epoch_number: rng.next_u64() };
        println!("pk_powers: {:?}", pk.powers_of_beta_g.len());
        println!("pk.powers(): {:?}", pk.powers().powers_of_beta_g.len());
        let epoch_challenge = CoinbasePuzzle::init_for_epoch(&epoch_info, degree);
        for batch_size in 1..10 {
            let solutions = (1..batch_size)
                .map(|_| {
                    let address = Address(<[u8; 32]>::rand(&mut rng));
                    let nonce = u64::rand(&mut rng);
                    CoinbasePuzzle::prove(&pk, &epoch_info, &epoch_challenge, &address, nonce)
                })
                .collect::<Vec<_>>();
            let full_solution = CoinbasePuzzle::accumulate(&pk, &epoch_info, &epoch_challenge, &solutions);
            assert!(CoinbasePuzzle::verify(&vk, &epoch_info, &epoch_challenge, &full_solution));
        }
    }
}
