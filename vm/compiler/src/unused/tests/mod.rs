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

use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::Duration,
};

use snarkvm_algorithms::{
    snark::marlin::{ahp::AHPForR1CS, CircuitProvingKey, MarlinHidingMode, MarlinNonHidingMode},
    SNARKError,
    SNARK,
    SRS,
};
use snarkvm_curves::bls12_377::{Bls12_377, Fr};
use snarkvm_dpc::{testnet2::Testnet2, BlockTemplate, Network, PoSWError, PoSWScheme};

use rand::{rngs::ThreadRng, thread_rng};

#[test]
fn test_posw_terminate() {
    // Construct the block template.
    let block = Testnet2::genesis_block();
    let block_template = BlockTemplate::new(
        block.previous_block_hash(),
        block.height(),
        block.timestamp(),
        block.difficulty_target(),
        block.cumulative_weight(),
        block.previous_ledger_root(),
        block.transactions().clone(),
        block.to_coinbase_transaction().unwrap().to_records().next().unwrap(),
    );

    let thread_terminator = Arc::new(AtomicBool::new(false));
    std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(1));
        thread_terminator.store(true, Ordering::SeqCst);
    });
    let result = Testnet2::posw().mine(&block_template, &AtomicBool::new(true), &mut thread_rng());

    assert!(matches!(result, Err(PoSWError::SNARKError(SNARKError::Terminated))));
}

/// TODO (howardwu): Update this when testnet2 is live.
#[ignore]
#[test]
fn test_posw_verify_testnet1() {
    // // Source from testnet1 block #171888.
    // // https://www.aleo.network/block/171888
    // pub const POSW_NONCE: u32 = 3395832407;
    // pub const POSW_PEDERSEN_MERKLE_ROOT: &str = "03d435625cd5673e031782c359bf22794bec6444d99c6bafa9e631edd3387c02";
    // pub const POSW_PROOF: &str = "03000000000000000400000000000000ccaaf4db06ebc84fca44d0271f0779d896fc644f2e1bb8e5c168cb753f52dff719229257b1f7860832e23b795944af800094ecf84d181ec27cead686d283a4e806049bda7cb8b2abb6f839aa86acaa310fc68d4ec436777f7cf7f8b02d97d01480002d01836267a6b4003a6525a8e9ee1cfedd3746c7f303b4438621bd7fcf17a12b26e1766af0c5c5fd297a2f805e736c0000b7e01d883aabcb46ce416d0a4803a3e2330e6d00095be0c66377b9eb675ab2537c7443aff545bcc9c3e3328c267f160100030000000000000017168c550f052fb8ebead88893b99fa97f4babefde90d4cb1d392c810721291bb505409f1fc1fc4b7b87caae50d28b8000af74350ba96787821b971f1daf83177409984f810238e8adc4e8f032a32af50e460a3b074de230f907e15ce6c3fca40101bfcea80a78bb74cbe4317075de34f1b2ceeeb384ad75b52208008ca699ab3d000ee3f14cd975da733ca444ddd5ecd900d03ff7f33331cb3e99545e1fe3750e532ffbd243ba4b43d85ee5ea9f644efb29d87e409d4bc195bbdf92f2671d9b40810002000000000000006b06964d98124cb6bed652b1e7cfd7d04dd247fcfc69388691d122f68c1804cb6f6880302034c2802c6863cd8959280101599587e22cb0ef2d59f0869fc494b89c3aae1abec5e59b7b2627b5ffbb157989cbd643e2be9483715e17a2a419d5ab00ad19d3771d58b2bdd24d57bcde654a393f70b5bcedc7ec5f195f4159c814bb3a87cbfc3d6ebe8cecc14a8a32f3994b0000070000000000000095d6d5040a519a2e187f462af3c1c3c11305da703fcb06a16933e0b5b5651a0a9f54cf588f44f5d627c4221f4c885cb216e385081ac986aee393104b7fb6970446d278f498e3c7866998339f123a722a46cd09a3a4b1db423fbc9f9b037bea108a0ec80747dbba9dc0f0c8d68737b83831b41d8d46992687d840ed1ccee9a4100a154925e9dc041432dd05b7523ab77366d34a36a384a007caf3443d99183a11c34cffd9d78a5088f00add5524a704868bce59bc102df87c9c216501185c96072fe56d081682568638675b5590ebca6913e21fddfdc8bee35f42310c1d8a75080300000000000000000000000000000000000000000000000000000000000000020000000000000032e4b5d04c6487b484307e3c77dc7de4e707b60106504bf26a8c6edd9b10fd59f7ee25d3d5ff2fb1cc00cf09686b3c800106fe9875aa0ba61ec8b913aba6dcb36020e04222bff8ed6f25f3c6986d36ce09643737802f65c295b39026bd6337cdcef06096509e33f1d32a5b4c5ffcb958f56e919964584129f50f0d6f1c160c82800000";
    //
    // // TODO (howardwu): Update this when testnet2 is live.
    // let difficulty_target = u64::MAX;
    //
    // let nonce = POSW_NONCE;
    // let root = {
    //     let bytes = hex::decode(POSW_PEDERSEN_MERKLE_ROOT).unwrap();
    //     assert_eq!(bytes.len(), 32);
    //     FromBytes::read_le(&bytes[..]).unwrap()
    // };
    // let proof = {
    //     let bytes = hex::decode(POSW_PROOF).unwrap();
    //     assert_eq!(bytes.len(), 972); // NOTE: Marlin proofs use compressed serialization
    //     <<Testnet1 as Network>::PoSWSNARK as SNARK>::Proof::read_le(&bytes[..]).unwrap()
    // };
    //
    // let posw = PoswMarlin::<Testnet1>::load(true).unwrap();
    // assert!(posw.verify(nonce, &root, difficulty_target, &proof));
}

#[test]
fn test_posw_setup_vs_load_weak_sanity_check() {
    let generated_posw: <Testnet2 as Network>::PoSW = {
        // Load the PoSW Marlin parameters.
        let rng = &mut thread_rng();
        // Run the universal setup.
        let max_degree = AHPForR1CS::<Fr, MarlinHidingMode>::max_degree(40000, 40000, 60000).unwrap();
        let universal_srs = <Testnet2 as Network>::PoSWSNARK::universal_setup(&max_degree, rng).unwrap();
        // Run the circuit setup.
        <<Testnet2 as Network>::PoSW as PoSWScheme<Testnet2>>::setup::<ThreadRng>(&mut SRS::<ThreadRng, _>::Universal(
            &universal_srs,
        ))
        .unwrap()
    };
    let loaded_posw = Testnet2::posw().clone();

    let generated_proving_key: &CircuitProvingKey<Bls12_377, MarlinNonHidingMode> =
        generated_posw.proving_key().as_ref().unwrap();
    let loaded_proving_key: &CircuitProvingKey<Bls12_377, MarlinNonHidingMode> =
        loaded_posw.proving_key().as_ref().unwrap();

    let a = generated_proving_key.committer_key.max_degree;
    let b = loaded_proving_key.committer_key.max_degree;
    assert_eq!(a, b);

    let a = generated_proving_key.circuit_commitment_randomness.len();
    let b = loaded_proving_key.circuit_commitment_randomness.len();
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    let a = generated_proving_key.circuit.max_degree();
    let b = loaded_proving_key.circuit.max_degree();
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    let a = generated_proving_key.circuit.index_info.num_variables;
    let b = loaded_proving_key.circuit.index_info.num_variables;
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    let a = generated_proving_key.circuit.index_info.num_constraints;
    let b = loaded_proving_key.circuit.index_info.num_constraints;
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    let a = generated_proving_key.circuit.index_info.num_non_zero_a;
    let b = loaded_proving_key.circuit.index_info.num_non_zero_a;
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    let a = generated_proving_key.circuit.index_info.num_non_zero_b;
    let b = loaded_proving_key.circuit.index_info.num_non_zero_b;
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    let a = generated_proving_key.circuit.index_info.num_non_zero_c;
    let b = loaded_proving_key.circuit.index_info.num_non_zero_c;
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    let a = generated_proving_key.circuit.index_info.max_degree::<MarlinHidingMode>();
    let b = loaded_proving_key.circuit.index_info.max_degree::<MarlinHidingMode>();
    println!("{:?} == {:?}? {}", a, b, a == b);
    assert_eq!(a, b);

    macro_rules! check_term_sizes {
        ($term: ident) => {
            let a = generated_proving_key.circuit.$term.len();
            let b = loaded_proving_key.circuit.$term.len();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            // TODO (howardwu): CRITICAL - Confirm expected circuit behavior and reenable inner checks.
            // for i in 0..generated_proving_key.circuit.$term.len() {
            //     let a = generated_proving_key.circuit.$term[i].len();
            //     let b = loaded_proving_key.circuit.$term[i].len();
            //     println!("{:?} == {:?}? {}", a, b, a == b);
            //     assert_eq!(a, b);
            // }
        };
    }

    check_term_sizes!(a);
    check_term_sizes!(b);
    check_term_sizes!(c);

    macro_rules! check_arithmetization_sizes {
        ($term: ident) => {
            let a = generated_proving_key.circuit.$term.row.degree_bound();
            let b = loaded_proving_key.circuit.$term.row.degree_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.row.hiding_bound();
            let b = loaded_proving_key.circuit.$term.row.hiding_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.row.polynomial().degree();
            let b = loaded_proving_key.circuit.$term.row.polynomial().degree();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.col.degree_bound();
            let b = loaded_proving_key.circuit.$term.col.degree_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.col.hiding_bound();
            let b = loaded_proving_key.circuit.$term.col.hiding_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.col.polynomial().degree();
            let b = loaded_proving_key.circuit.$term.col.polynomial().degree();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.val.degree_bound();
            let b = loaded_proving_key.circuit.$term.val.degree_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.val.hiding_bound();
            let b = loaded_proving_key.circuit.$term.val.hiding_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.val.polynomial().degree();
            let b = loaded_proving_key.circuit.$term.val.polynomial().degree();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.row_col.degree_bound();
            let b = loaded_proving_key.circuit.$term.row_col.degree_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.row_col.hiding_bound();
            let b = loaded_proving_key.circuit.$term.row_col.hiding_bound();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.row_col.polynomial().degree();
            let b = loaded_proving_key.circuit.$term.row_col.polynomial().degree();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.evals_on_K.row.evaluations.len();
            let b = loaded_proving_key.circuit.$term.evals_on_K.row.evaluations.len();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.evals_on_K.col.evaluations.len();
            let b = loaded_proving_key.circuit.$term.evals_on_K.col.evaluations.len();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.evals_on_K.row_col.evaluations.len();
            let b = loaded_proving_key.circuit.$term.evals_on_K.row_col.evaluations.len();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);

            let a = generated_proving_key.circuit.$term.evals_on_K.val.evaluations.len();
            let b = loaded_proving_key.circuit.$term.evals_on_K.val.evaluations.len();
            println!("{:?} == {:?}? {}", a, b, a == b);
            assert_eq!(a, b);
        };
    }

    println!("------ Checking circuit arithmetization size ------");
    check_arithmetization_sizes!(a_arith);
    check_arithmetization_sizes!(b_arith);
    check_arithmetization_sizes!(c_arith);
}
