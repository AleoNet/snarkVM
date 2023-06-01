window.BENCHMARK_DATA = {
  "lastUpdate": 1685655230640,
  "repoUrl": "https://github.com/AleoHQ/snarkVM",
  "entries": {
    "snarkVM Benchmarks": [
      {
        "commit": {
          "author": {
            "name": "AleoHQ",
            "username": "AleoHQ"
          },
          "committer": {
            "name": "AleoHQ",
            "username": "AleoHQ"
          },
          "id": "bff4f3d7553d0f69bf285d46fe03e9264c41e40e",
          "message": "Introduce Continuous Benchmarking",
          "timestamp": "2023-03-19T09:22:07Z",
          "url": "https://github.com/AleoHQ/snarkVM/pull/1401/commits/bff4f3d7553d0f69bf285d46fe03e9264c41e40e"
        },
        "date": 1679340893168,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 116407048,
            "range": "± 3164171",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 820867863,
            "range": "± 16297076",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1504786437,
            "range": "± 59456912",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 2315463932,
            "range": "± 37281752",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2938928317,
            "range": "± 40201054",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 3360629035,
            "range": "± 40466065",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 6095637842,
            "range": "± 297703087",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 11058697222,
            "range": "± 83503185",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 78206258,
            "range": "± 1736546",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 579259797,
            "range": "± 13165664",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 5051817612,
            "range": "± 111948041",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 107118,
            "range": "± 6927",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 261453,
            "range": "± 16420",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1949077702,
            "range": "± 25604932",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 110474751,
            "range": "± 4133780",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 666384736,
            "range": "± 14034454",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 11104315683,
            "range": "± 281649966",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 8003907,
            "range": "± 233138",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 21660000,
            "range": "± 318282",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 179532753,
            "range": "± 3189046",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 1099760463,
            "range": "± 32831559",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 8247076,
            "range": "± 236127",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 10453380,
            "range": "± 437386",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 40835161,
            "range": "± 1809159",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 289659623,
            "range": "± 10422013",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 13900808,
            "range": "± 307831",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 449398,
            "range": "± 12166",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 1139169740,
            "range": "± 15980413",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 116528,
            "range": "± 4425",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 214473,
            "range": "± 5754",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 278770,
            "range": "± 7878",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 81416,
            "range": "± 3695",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 80753,
            "range": "± 4042",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 157030,
            "range": "± 6335",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 192153,
            "range": "± 5620",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 238363,
            "range": "± 12616",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 89645,
            "range": "± 4012",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 89305,
            "range": "± 4281",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 181417,
            "range": "± 10926",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 185279,
            "range": "± 17243",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 219371,
            "range": "± 9778",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 198982,
            "range": "± 7072",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 200454,
            "range": "± 8552",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 309663,
            "range": "± 11764",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 312762,
            "range": "± 18536",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 301860,
            "range": "± 9683",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::new (10 leaves)",
            "value": 6462420,
            "range": "± 156338",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::new (100 leaves)",
            "value": 25971328,
            "range": "± 1064595",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::new (1000 leaves)",
            "value": 127819805,
            "range": "± 3880599",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::new (10000 leaves)",
            "value": 1520327697,
            "range": "± 29679840",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding single leaf to a tree with 10 leaves)",
            "value": 4224632,
            "range": "± 152993",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 10 new leaves to a tree with 10 leaves)",
            "value": 7146247,
            "range": "± 149267",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 100 new leaves to a tree with 10 leaves)",
            "value": 25994506,
            "range": "± 1007112",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 1000 new leaves to a tree with 10 leaves)",
            "value": 123095979,
            "range": "± 3468593",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding single leaf to a tree with 100 leaves)",
            "value": 3974001,
            "range": "± 54232",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 10 new leaves to a tree with 100 leaves)",
            "value": 6007453,
            "range": "± 398670",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 100 new leaves to a tree with 100 leaves)",
            "value": 30126172,
            "range": "± 805216",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 1000 new leaves to a tree with 100 leaves)",
            "value": 178664855,
            "range": "± 4079870",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding single leaf to a tree with 1000 leaves)",
            "value": 4356854,
            "range": "± 214238",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 10 new leaves to a tree with 1000 leaves)",
            "value": 5751837,
            "range": "± 223149",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 100 new leaves to a tree with 1000 leaves)",
            "value": 84015496,
            "range": "± 2703136",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 1000 new leaves to a tree with 1000 leaves)",
            "value": 129627366,
            "range": "± 3892306",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding single leaf to a tree with 10000 leaves)",
            "value": 4902216,
            "range": "± 263038",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 10 new leaves to a tree with 10000 leaves)",
            "value": 6602041,
            "range": "± 140216",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 100 new leaves to a tree with 10000 leaves)",
            "value": 24369768,
            "range": "± 1235915",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree::append (adding 1000 new leaves to a tree with 10000 leaves)",
            "value": 121124380,
            "range": "± 1896505",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 197604,
            "range": "± 9295",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 149101,
            "range": "± 11279",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 1140,
            "range": "± 62",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 871,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 548,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 91658,
            "range": "± 5726",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1908335,
            "range": "± 62463",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 450575,
            "range": "± 24079",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 4432,
            "range": "± 280",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 3054,
            "range": "± 175",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1969,
            "range": "± 99",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 14,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 15,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 18,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 74,
            "range": "± 8",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 14,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 65,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 11452,
            "range": "± 468",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 82768,
            "range": "± 3731",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 44,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 78,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 247,
            "range": "± 40",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 149,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 6497,
            "range": "± 306",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 177,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 4471,
            "range": "± 248",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 23869,
            "range": "± 974",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 25,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 263,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 22,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 210,
            "range": "± 8",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 12518,
            "range": "± 654",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 135629,
            "range": "± 26337",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 40,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 38,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6235,
            "range": "± 510",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 33981,
            "range": "± 2433",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 25,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 37,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 570136,
            "range": "± 49220",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 1106272,
            "range": "± 69146",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 2084326,
            "range": "± 161814",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 9271583813,
            "range": "± 138961811",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 372132915,
            "range": "± 10597370",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 311651642,
            "range": "± 4381629",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1528949375,
            "range": "± 48753381",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 500 of 2^13",
            "value": 6940986052,
            "range": "± 167902107",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Verify 10 of 2^13",
            "value": 149170162,
            "range": "± 4666514",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Verify 100 of 2^13",
            "value": 1332171243,
            "range": "± 108257180",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Verify 500 of 2^13",
            "value": 6734071035,
            "range": "± 208135953",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "65319dd73144a99ecbeda267b5d5bb86e2599f7f",
          "message": "Merge pull request #1608 from AleoHQ/update/reduce-merkle-tree-benchmarks\n\nReduce sizes in `merkle_tree` benchmarks",
          "timestamp": "2023-05-30T14:24:09-07:00",
          "tree_id": "52873a6d5943d070516e96ae2ed83f07e41ecc17",
          "url": "https://github.com/AleoHQ/snarkVM/commit/65319dd73144a99ecbeda267b5d5bb86e2599f7f"
        },
        "date": 1685493785077,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 109452808,
            "range": "± 3999241",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 765645023,
            "range": "± 2045568",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1396154423,
            "range": "± 4253488",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 2155215853,
            "range": "± 9952235",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2728960888,
            "range": "± 13290635",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 3068952136,
            "range": "± 34575123",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 5629641847,
            "range": "± 15790299",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 10076638329,
            "range": "± 17903175",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 71815468,
            "range": "± 577257",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 530395321,
            "range": "± 1953517",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 5064071583,
            "range": "± 108157744",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 97083,
            "range": "± 210",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 241332,
            "range": "± 522",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1730323301,
            "range": "± 5751258",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 103354268,
            "range": "± 920488",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 642446676,
            "range": "± 34071622",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 10538715248,
            "range": "± 29448888",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 8186,
            "range": "± 41",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 8509,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 31253746,
            "range": "± 906444",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 14330080,
            "range": "± 51751",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 22786772,
            "range": "± 386682",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 6118801,
            "range": "± 6767",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 7712800,
            "range": "± 112489",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 20245260,
            "range": "± 776946",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 166868265,
            "range": "± 647932",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 1011728400,
            "range": "± 4756917",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 7860567,
            "range": "± 72040",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 9639599,
            "range": "± 72323",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 35912391,
            "range": "± 1016031",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 255923166,
            "range": "± 6912855",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 8387517,
            "range": "± 12887",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 405837,
            "range": "± 667",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 847018522,
            "range": "± 2613320",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 107894,
            "range": "± 72",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 207467,
            "range": "± 5777",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 272508,
            "range": "± 8732",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 76904,
            "range": "± 199",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 76822,
            "range": "± 113",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 154345,
            "range": "± 234",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 179890,
            "range": "± 191",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 231384,
            "range": "± 620",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 90693,
            "range": "± 416",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 90684,
            "range": "± 120",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 181437,
            "range": "± 488",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 181236,
            "range": "± 258",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 227017,
            "range": "± 219",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 202632,
            "range": "± 598",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 202731,
            "range": "± 461",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 305600,
            "range": "± 374",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 305517,
            "range": "± 444",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 305543,
            "range": "± 172",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 4134030,
            "range": "± 1351",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 6243699,
            "range": "± 2237",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 26966935,
            "range": "± 12926",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 125206887,
            "range": "± 2262227",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1468327850,
            "range": "± 10901997",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 12444546324,
            "range": "± 39954529",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 4013868,
            "range": "± 2559",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 6127481,
            "range": "± 3277",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 26809840,
            "range": "± 57460",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 121849581,
            "range": "± 1833348",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1458303069,
            "range": "± 4604993",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 12460230143,
            "range": "± 26085046",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 4011631,
            "range": "± 2948",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 6952752,
            "range": "± 3532",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 25908880,
            "range": "± 22195",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 122645991,
            "range": "± 2104733",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1456759512,
            "range": "± 9175105",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 12434459877,
            "range": "± 30759586",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 4011539,
            "range": "± 2123",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 5637446,
            "range": "± 3237",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 30286186,
            "range": "± 48753",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 177224866,
            "range": "± 2603277",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1456552460,
            "range": "± 5193516",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 12428813963,
            "range": "± 12582980",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 4026052,
            "range": "± 3239",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 5772152,
            "range": "± 2520",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 83155580,
            "range": "± 318957",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 124995883,
            "range": "± 1897828",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1401595862,
            "range": "± 11605344",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 12361806721,
            "range": "± 16131392",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 4271095,
            "range": "± 18240",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 5902093,
            "range": "± 12850",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 24301132,
            "range": "± 36391",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 124880100,
            "range": "± 2440165",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1844184999,
            "range": "± 5875317",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 11860364854,
            "range": "± 39853878",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 6745478,
            "range": "± 824371",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 8694135,
            "range": "± 847857",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 28720082,
            "range": "± 813761",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 124803483,
            "range": "± 1529763",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 1084609382,
            "range": "± 7602304",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 14389198301,
            "range": "± 34669327",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 4015841,
            "range": "± 2174",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 40152556,
            "range": "± 50633",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 401635122,
            "range": "± 133014",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 4014926402,
            "range": "± 1219968",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 40162275040,
            "range": "± 3490633",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 4008827,
            "range": "± 2107",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 40153802,
            "range": "± 18529",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 401945362,
            "range": "± 171471",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 4016019685,
            "range": "± 595281",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 40194287168,
            "range": "± 3951148",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 4015264,
            "range": "± 3404",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 40171015,
            "range": "± 27589",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 401839868,
            "range": "± 445126",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 4018886393,
            "range": "± 704404",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 40187133700,
            "range": "± 9320199",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 4019841,
            "range": "± 1638",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 40195984,
            "range": "± 18270",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 402224576,
            "range": "± 166121",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 4024278146,
            "range": "± 623955",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 40227632465,
            "range": "± 4029148",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 4189100,
            "range": "± 7125",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 41755881,
            "range": "± 67923",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 417945656,
            "range": "± 477979",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 4172744164,
            "range": "± 2931641",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 41803168217,
            "range": "± 74462211",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 6088633,
            "range": "± 163332",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 54932772,
            "range": "± 644204",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 539470199,
            "range": "± 4971648",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 5447508387,
            "range": "± 54416340",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 54523233512,
            "range": "± 180326882",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3998992,
            "range": "± 2194",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3997216,
            "range": "± 3141",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 3999027,
            "range": "± 2319",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 3997843,
            "range": "± 2190",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 3999586,
            "range": "± 2718",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 3997170,
            "range": "± 1301",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 5642501,
            "range": "± 3023",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 5638291,
            "range": "± 4637",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 5637820,
            "range": "± 3110",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 5643049,
            "range": "± 5555",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 3990802,
            "range": "± 2744",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 5877821,
            "range": "± 2904",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 24075807,
            "range": "± 109378",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 24074906,
            "range": "± 118760",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 24064153,
            "range": "± 94800",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 3994912,
            "range": "± 2884",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 5882216,
            "range": "± 1793",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 24075316,
            "range": "± 100435",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 124718295,
            "range": "± 2094620",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 124151096,
            "range": "± 2666169",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 4028939,
            "range": "± 4539",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 5807356,
            "range": "± 9039",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 26487253,
            "range": "± 80509",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 138170900,
            "range": "± 1857677",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8641",
            "value": 1049675723,
            "range": "± 6677579",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 4158389,
            "range": "± 51385",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 7161003,
            "range": "± 36859",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 46431876,
            "range": "± 20624",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 250587199,
            "range": "± 1249971",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 2387906493,
            "range": "± 22726848",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 3994154,
            "range": "± 2248",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 3996025,
            "range": "± 1826",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3993493,
            "range": "± 2180",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3997403,
            "range": "± 6817",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3990382,
            "range": "± 2225",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 3992496,
            "range": "± 886",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 3994506,
            "range": "± 2516",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3995227,
            "range": "± 3026",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3993496,
            "range": "± 2246",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 3994990,
            "range": "± 1443",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 3990577,
            "range": "± 3239",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 3993133,
            "range": "± 1840",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 3990259,
            "range": "± 2798",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 3991203,
            "range": "± 1398",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3995494,
            "range": "± 1863",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 3996390,
            "range": "± 1334",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 3993924,
            "range": "± 2799",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 3995167,
            "range": "± 2772",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 3997604,
            "range": "± 3408",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 3995586,
            "range": "± 2024",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 4008229,
            "range": "± 2882",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 3994999,
            "range": "± 5109",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 4026473,
            "range": "± 3418",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 3995323,
            "range": "± 1361",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 4079336,
            "range": "± 3012",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3999759,
            "range": "± 2399",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 4164896,
            "range": "± 7520",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3999885,
            "range": "± 5264",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 4362012,
            "range": "± 23510",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 4006765,
            "range": "± 9247",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4788922,
            "range": "± 70901",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 4018112,
            "range": "± 19550",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 189992,
            "range": "± 3378",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 212395,
            "range": "± 21047",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 1150,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 821,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 530,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 90924,
            "range": "± 147",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1827137,
            "range": "± 10351",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 504913,
            "range": "± 19068",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 4322,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 3072,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1937,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 17,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 70,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 64,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 13117,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 79949,
            "range": "± 180",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 42,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 81,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 246,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 144,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 6405,
            "range": "± 41",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 167,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 4460,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 24966,
            "range": "± 68",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 27,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 258,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 21,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 208,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 14091,
            "range": "± 19",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 130297,
            "range": "± 4939",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 9,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 37,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 36,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6936,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 34290,
            "range": "± 57",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 23,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 38,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 593826,
            "range": "± 1159",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 1190857,
            "range": "± 3165",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 2097266,
            "range": "± 3201",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 8707541866,
            "range": "± 82669817",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 334259421,
            "range": "± 2092442",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 291499913,
            "range": "± 1869323",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1429613466,
            "range": "± 5936386",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "distinct": true,
          "id": "15672568e89833991ccbee8a76d68ee5515992ad",
          "message": "chore(snarkvm): bump version for new release",
          "timestamp": "2023-05-30T15:06:37-07:00",
          "tree_id": "8bbba5e535209e323e341529efbb00751f2987ec",
          "url": "https://github.com/AleoHQ/snarkVM/commit/15672568e89833991ccbee8a76d68ee5515992ad"
        },
        "date": 1685494765190,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 90922439,
            "range": "± 280085",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 638095761,
            "range": "± 2033520",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1172839217,
            "range": "± 5874473",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 1802526659,
            "range": "± 3648229",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2287398995,
            "range": "± 6524029",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 2589679615,
            "range": "± 4451764",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 4762574926,
            "range": "± 12746959",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 8513030765,
            "range": "± 14199174",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 60014840,
            "range": "± 232096",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 446814769,
            "range": "± 5777380",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 4465601390,
            "range": "± 22804803",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 80384,
            "range": "± 33",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 200677,
            "range": "± 72",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1465550355,
            "range": "± 4141145",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 86533858,
            "range": "± 1406985",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 531510330,
            "range": "± 1529908",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 8771782951,
            "range": "± 27189342",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 6732,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 7026,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 25823586,
            "range": "± 316309",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 12013300,
            "range": "± 5843",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 19004036,
            "range": "± 338070",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 5204113,
            "range": "± 3209",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 6378140,
            "range": "± 23267",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 16790841,
            "range": "± 48637",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 140152404,
            "range": "± 774766",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 864876834,
            "range": "± 2745784",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 6648568,
            "range": "± 44288",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 8201319,
            "range": "± 53505",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 30932028,
            "range": "± 1022217",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 241205646,
            "range": "± 1637632",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 6938489,
            "range": "± 9475",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 338117,
            "range": "± 955",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 847710911,
            "range": "± 1160112",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 89030,
            "range": "± 49",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 172708,
            "range": "± 4326",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 222923,
            "range": "± 5862",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 63564,
            "range": "± 75",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 63552,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 127678,
            "range": "± 254",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 149434,
            "range": "± 35",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 191411,
            "range": "± 50",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 74836,
            "range": "± 122",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 74842,
            "range": "± 88",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 150413,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 150162,
            "range": "± 38",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 187852,
            "range": "± 1206",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 167847,
            "range": "± 52",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 167732,
            "range": "± 41",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 252609,
            "range": "± 86",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 252465,
            "range": "± 226",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 252653,
            "range": "± 278",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 3436311,
            "range": "± 1029",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 5189889,
            "range": "± 846",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 22427808,
            "range": "± 35871",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 104074900,
            "range": "± 1893916",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1209081831,
            "range": "± 5873038",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 10284203315,
            "range": "± 18955492",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 3343184,
            "range": "± 489",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 5101520,
            "range": "± 1513",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 22325016,
            "range": "± 28396",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 103386361,
            "range": "± 2549447",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1215048279,
            "range": "± 5485035",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 10308537466,
            "range": "± 28232228",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 3340627,
            "range": "± 864",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 5780921,
            "range": "± 1910",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 21552641,
            "range": "± 7234",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 104026933,
            "range": "± 2448384",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1209755636,
            "range": "± 5670367",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 10305217339,
            "range": "± 23652773",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 3342069,
            "range": "± 940",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 4691559,
            "range": "± 1213",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 25216408,
            "range": "± 17359",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 148034221,
            "range": "± 1932963",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1200185520,
            "range": "± 8253460",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 10278493132,
            "range": "± 21884725",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 3347170,
            "range": "± 1229",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 4796526,
            "range": "± 3091",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 72110232,
            "range": "± 903165",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 103857056,
            "range": "± 2469934",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1157383824,
            "range": "± 5242610",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 10258627185,
            "range": "± 37301367",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 3546254,
            "range": "± 12915",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 4874270,
            "range": "± 6957",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 20134239,
            "range": "± 34647",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 102527272,
            "range": "± 2612842",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1518705061,
            "range": "± 6011242",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 9762783222,
            "range": "± 26819358",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 5706997,
            "range": "± 632780",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 7073482,
            "range": "± 696923",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 23820237,
            "range": "± 693031",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 111888141,
            "range": "± 4599085",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 887339840,
            "range": "± 2194235",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 11853127584,
            "range": "± 13914791",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 3340308,
            "range": "± 939",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 33374770,
            "range": "± 27407",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 333797315,
            "range": "± 57233",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 3337321559,
            "range": "± 1171149",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 33375904453,
            "range": "± 3597877",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 3334830,
            "range": "± 932",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 33389913,
            "range": "± 8476",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 332406824,
            "range": "± 428674",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 3338503342,
            "range": "± 232887",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 33412998187,
            "range": "± 6842010",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 3338980,
            "range": "± 1071",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 33420417,
            "range": "± 12364",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 333914963,
            "range": "± 40930",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 3338058879,
            "range": "± 902288",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 33413050374,
            "range": "± 7688289",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 3344404,
            "range": "± 1890",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 33449150,
            "range": "± 15033",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 334393517,
            "range": "± 31380",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 3342387845,
            "range": "± 1351809",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 33472049399,
            "range": "± 4263611",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 3491004,
            "range": "± 6898",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 34716201,
            "range": "± 24271",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 346593955,
            "range": "± 92903",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 3471301700,
            "range": "± 2144888",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 34694130648,
            "range": "± 47113396",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 4869199,
            "range": "± 169382",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 42454341,
            "range": "± 147075",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 425460674,
            "range": "± 7980347",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 4338781751,
            "range": "± 59377142",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 42592987993,
            "range": "± 181842939",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3322803,
            "range": "± 669",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3324250,
            "range": "± 597",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 3325522,
            "range": "± 767",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 3324222,
            "range": "± 1450",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 3324266,
            "range": "± 1424",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 3322918,
            "range": "± 769",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 4671047,
            "range": "± 950",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 4648795,
            "range": "± 14837",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 4673019,
            "range": "± 1122",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 4675225,
            "range": "± 892",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 3318649,
            "range": "± 2235",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 4871193,
            "range": "± 910",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 19797907,
            "range": "± 9497",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 19815822,
            "range": "± 9086",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 19809783,
            "range": "± 8987",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 3319559,
            "range": "± 840",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 4869694,
            "range": "± 780",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 19808466,
            "range": "± 9071",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 103130243,
            "range": "± 2353106",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 103523697,
            "range": "± 3074117",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 3343782,
            "range": "± 5520",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 4696474,
            "range": "± 3876",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 22598775,
            "range": "± 29402",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 112937334,
            "range": "± 2046331",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8681",
            "value": 866985607,
            "range": "± 6251749",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 3462592,
            "range": "± 44359",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 6973116,
            "range": "± 48412",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 38956204,
            "range": "± 129779",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 207139334,
            "range": "± 1855039",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 1951625325,
            "range": "± 8092665",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 3322528,
            "range": "± 1010",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 3320527,
            "range": "± 909",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3321135,
            "range": "± 986",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3322532,
            "range": "± 1128",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3322522,
            "range": "± 2099",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 3323626,
            "range": "± 776",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 3322195,
            "range": "± 528",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3322974,
            "range": "± 381",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3322643,
            "range": "± 794",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 3323016,
            "range": "± 1101",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 3322169,
            "range": "± 1475",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 3324311,
            "range": "± 2122",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 3320397,
            "range": "± 711",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 3323348,
            "range": "± 909",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3306190,
            "range": "± 1637",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 3322805,
            "range": "± 1596",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 3323362,
            "range": "± 1599",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 3322913,
            "range": "± 1699",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 3326459,
            "range": "± 2132",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 3322343,
            "range": "± 3998",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 3334196,
            "range": "± 3590",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 3325042,
            "range": "± 1357",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 3344052,
            "range": "± 2561",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 3324515,
            "range": "± 991",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 3385431,
            "range": "± 4936",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3323047,
            "range": "± 918",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 3467168,
            "range": "± 14741",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3327658,
            "range": "± 3530",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 3612030,
            "range": "± 10738",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 3326848,
            "range": "± 7490",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 3997354,
            "range": "± 60503",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 3341743,
            "range": "± 21555",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 158270,
            "range": "± 2752",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 175699,
            "range": "± 5755",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 942,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 685,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 440,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 74474,
            "range": "± 42",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1530536,
            "range": "± 7318",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 414703,
            "range": "± 4177",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 3593,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 2556,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1616,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 11,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 15,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 59,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 11,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 53,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 10916,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 66547,
            "range": "± 102",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 35,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 67,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 205,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 121,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 5328,
            "range": "± 16",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 140,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 3707,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 20701,
            "range": "± 54",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 22,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 217,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 18,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 172,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 11701,
            "range": "± 34",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 111480,
            "range": "± 8323",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 3,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 33,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 31,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 5677,
            "range": "± 19",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 28546,
            "range": "± 70",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 21,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 33,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 493901,
            "range": "± 1381",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 992448,
            "range": "± 3882",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 1709514,
            "range": "± 4760",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 7150666080,
            "range": "± 19158086",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 276397318,
            "range": "± 686566",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 242157002,
            "range": "± 966586",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1183832848,
            "range": "± 33760456",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "137a0a87f20aca691775979b59910994e870b8d0",
          "message": "Merge pull request #1609 from AleoHQ/prelude/syn",
          "timestamp": "2023-05-30T15:04:55-07:00",
          "tree_id": "54fe01e57f44b31a5d9874ac6f154e51526ec663",
          "url": "https://github.com/AleoHQ/snarkVM/commit/137a0a87f20aca691775979b59910994e870b8d0"
        },
        "date": 1685496467922,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 115172902,
            "range": "± 1539204",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 817711698,
            "range": "± 25252570",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1494494603,
            "range": "± 21087994",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 2313894287,
            "range": "± 40079858",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2902594908,
            "range": "± 29645038",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 3317255512,
            "range": "± 52794112",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 6021235520,
            "range": "± 76222334",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 10918208356,
            "range": "± 94521969",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 75569316,
            "range": "± 979380",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 565017021,
            "range": "± 22516636",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 5061303309,
            "range": "± 109833786",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 102836,
            "range": "± 5578",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 264204,
            "range": "± 11600",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1862085210,
            "range": "± 21463402",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 109065884,
            "range": "± 2131093",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 666126381,
            "range": "± 9701787",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 10995947189,
            "range": "± 106198070",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 8676,
            "range": "± 311",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 8689,
            "range": "± 97",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 32515659,
            "range": "± 1016357",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 14880737,
            "range": "± 393121",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 23620555,
            "range": "± 980716",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 6375554,
            "range": "± 88227",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 8118053,
            "range": "± 173980",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 21320046,
            "range": "± 452298",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 175145922,
            "range": "± 2575364",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 1098441659,
            "range": "± 20930800",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 8428853,
            "range": "± 216925",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 10400922,
            "range": "± 214004",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 40306027,
            "range": "± 1549380",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 289576081,
            "range": "± 5013888",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 12649705,
            "range": "± 381583",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 442533,
            "range": "± 9678",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 1108043663,
            "range": "± 17296886",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 107290,
            "range": "± 2632",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 213855,
            "range": "± 8330",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 273038,
            "range": "± 9718",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 76439,
            "range": "± 3658",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 77534,
            "range": "± 3300",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 153922,
            "range": "± 5891",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 182202,
            "range": "± 23197",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 231037,
            "range": "± 8838",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 88773,
            "range": "± 3619",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 87624,
            "range": "± 4214",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 181101,
            "range": "± 7693",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 175517,
            "range": "± 7550",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 224287,
            "range": "± 8101",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 197825,
            "range": "± 10617",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 193663,
            "range": "± 8857",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 296979,
            "range": "± 16846",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 295000,
            "range": "± 14024",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 293121,
            "range": "± 13574",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 4073362,
            "range": "± 96518",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 6159759,
            "range": "± 45454",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 27437616,
            "range": "± 672181",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 127551873,
            "range": "± 2194392",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1465801459,
            "range": "± 22095172",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 12513890352,
            "range": "± 107614767",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 3991727,
            "range": "± 54094",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 6093985,
            "range": "± 118962",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 26784327,
            "range": "± 773231",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 122911388,
            "range": "± 1544766",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1457576168,
            "range": "± 15014425",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 12542481524,
            "range": "± 94166357",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 4019724,
            "range": "± 83024",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 7207473,
            "range": "± 173844",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 26323366,
            "range": "± 892133",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 123976195,
            "range": "± 1709070",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1456980595,
            "range": "± 18220624",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 12510108014,
            "range": "± 112914169",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 4102682,
            "range": "± 51148",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 5596318,
            "range": "± 120123",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 30029552,
            "range": "± 723034",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 180055021,
            "range": "± 4012456",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1463043699,
            "range": "± 17335176",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 12581756661,
            "range": "± 108906984",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 4042423,
            "range": "± 76503",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 5735708,
            "range": "± 82397",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 85445467,
            "range": "± 1777971",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 127077599,
            "range": "± 2337824",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1416490335,
            "range": "± 13035817",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 12440401499,
            "range": "± 70689821",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 4167501,
            "range": "± 96800",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 5882100,
            "range": "± 169389",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 23807092,
            "range": "± 394621",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 123254404,
            "range": "± 1854456",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1843837144,
            "range": "± 22821170",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 11860422380,
            "range": "± 100463759",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 7068182,
            "range": "± 539690",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 9188616,
            "range": "± 868972",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 29714748,
            "range": "± 793360",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 127679978,
            "range": "± 3071093",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 1096164569,
            "range": "± 12894521",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 14566698459,
            "range": "± 498368482",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 4072790,
            "range": "± 104036",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 40742792,
            "range": "± 683880",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 400693104,
            "range": "± 3757969",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 4057184654,
            "range": "± 45249902",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 40108024226,
            "range": "± 235945035",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 4008797,
            "range": "± 142947",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 39697814,
            "range": "± 1133280",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 404262145,
            "range": "± 9376778",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 4010846962,
            "range": "± 25159836",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 39906906128,
            "range": "± 211158185",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 3994637,
            "range": "± 106820",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 39878768,
            "range": "± 840438",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 409899887,
            "range": "± 15541550",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 4024659621,
            "range": "± 49391226",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 40344438979,
            "range": "± 264743989",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 3985440,
            "range": "± 136545",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 40399527,
            "range": "± 660563",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 408992993,
            "range": "± 7283796",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 3990439003,
            "range": "± 68234031",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 40162690728,
            "range": "± 247257553",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 4121667,
            "range": "± 83734",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 42443453,
            "range": "± 686731",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 429288608,
            "range": "± 7124922",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 4153816143,
            "range": "± 35282503",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 41803500299,
            "range": "± 295956697",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 6325672,
            "range": "± 417890",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 54300279,
            "range": "± 2089905",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 554744431,
            "range": "± 13122383",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 5478575825,
            "range": "± 79654611",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 54312948588,
            "range": "± 281985834",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 4197072,
            "range": "± 95134",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 4091500,
            "range": "± 115416",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 4205836,
            "range": "± 139620",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 4205804,
            "range": "± 196615",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 4111294,
            "range": "± 51071",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 4090064,
            "range": "± 57903",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 5651465,
            "range": "± 104339",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 5704604,
            "range": "± 120618",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 5790207,
            "range": "± 301208",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 5722089,
            "range": "± 204024",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 4067460,
            "range": "± 108209",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 5847275,
            "range": "± 90018",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 23660549,
            "range": "± 354471",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 23772792,
            "range": "± 241631",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 24040530,
            "range": "± 809543",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 4155950,
            "range": "± 110711",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 5961167,
            "range": "± 158334",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 23743260,
            "range": "± 417216",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 119223922,
            "range": "± 3858614",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 121449294,
            "range": "± 3782290",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 4192245,
            "range": "± 81343",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 5968845,
            "range": "± 142339",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 26638643,
            "range": "± 475988",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 136612149,
            "range": "± 4675873",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8638",
            "value": 1003020596,
            "range": "± 13169988",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 4403337,
            "range": "± 74219",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 7716783,
            "range": "± 216729",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 47040578,
            "range": "± 757990",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 239945062,
            "range": "± 4260097",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 2281343915,
            "range": "± 30383326",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 4003326,
            "range": "± 81675",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 3959129,
            "range": "± 47048",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 4011990,
            "range": "± 99300",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3946613,
            "range": "± 41386",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3930012,
            "range": "± 92828",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 4074972,
            "range": "± 95017",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 4012016,
            "range": "± 86763",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3995986,
            "range": "± 111548",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 4068278,
            "range": "± 125084",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 3976999,
            "range": "± 68631",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 4027256,
            "range": "± 80071",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 4062143,
            "range": "± 105300",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 4019428,
            "range": "± 32948",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 4097309,
            "range": "± 85949",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3982855,
            "range": "± 34581",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 3988362,
            "range": "± 56942",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 4062393,
            "range": "± 78407",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 4018908,
            "range": "± 97755",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 4056442,
            "range": "± 146563",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 3991672,
            "range": "± 178835",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 3943584,
            "range": "± 51777",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 4074368,
            "range": "± 154151",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 4011831,
            "range": "± 43347",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 4019286,
            "range": "± 64115",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 4091129,
            "range": "± 96787",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3997984,
            "range": "± 69376",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 4286190,
            "range": "± 111560",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3989291,
            "range": "± 60070",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 4420178,
            "range": "± 144250",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 3977698,
            "range": "± 47736",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4857426,
            "range": "± 152335",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 4132301,
            "range": "± 146742",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 192590,
            "range": "± 10918",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 216083,
            "range": "± 16632",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 1173,
            "range": "± 57",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 858,
            "range": "± 46",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 537,
            "range": "± 52",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 92362,
            "range": "± 8398",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1868099,
            "range": "± 114596",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 569316,
            "range": "± 67640",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 4385,
            "range": "± 240",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 3123,
            "range": "± 200",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 2014,
            "range": "± 118",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 17,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 73,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 17,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 66,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 11563,
            "range": "± 587",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 81641,
            "range": "± 4401",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 44,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 79,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 269,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 151,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 6556,
            "range": "± 3470",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 184,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 4639,
            "range": "± 285",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 23888,
            "range": "± 1239",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 23,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 262,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 21,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 218,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 12956,
            "range": "± 719",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 131833,
            "range": "± 15413",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 36,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 37,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6215,
            "range": "± 341",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 33051,
            "range": "± 1532",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 25,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 40,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 612530,
            "range": "± 26013",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 1197565,
            "range": "± 61906",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 2074960,
            "range": "± 82533",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 8830774606,
            "range": "± 103963846",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 344042493,
            "range": "± 6823604",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 299995789,
            "range": "± 6209862",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1480125313,
            "range": "± 13646271",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "14917648+raychu86@users.noreply.github.com",
            "name": "raychu86",
            "username": "raychu86"
          },
          "committer": {
            "email": "14917648+raychu86@users.noreply.github.com",
            "name": "raychu86",
            "username": "raychu86"
          },
          "distinct": true,
          "id": "d896844c8b4b6aaa9872814771c25866c242fe5d",
          "message": "Fix synthesizer benches",
          "timestamp": "2023-05-30T18:22:16-07:00",
          "tree_id": "862a8fbc1b98cb5c205a5fcbe954193214bc5cd1",
          "url": "https://github.com/AleoHQ/snarkVM/commit/d896844c8b4b6aaa9872814771c25866c242fe5d"
        },
        "date": 1685510026459,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 90309021,
            "range": "± 281055",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 651629743,
            "range": "± 6683182",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1216889369,
            "range": "± 3247211",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 1890370415,
            "range": "± 9103204",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2411470297,
            "range": "± 13934638",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 2826993928,
            "range": "± 13510510",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 5171529197,
            "range": "± 54956980",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 9245811591,
            "range": "± 22188518",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 59850400,
            "range": "± 223416",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 436937185,
            "range": "± 3390947",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 3984802804,
            "range": "± 91075741",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 80184,
            "range": "± 21",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 200604,
            "range": "± 63",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1633751258,
            "range": "± 4832236",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 85258286,
            "range": "± 441091",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 527266813,
            "range": "± 2424979",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 8683228065,
            "range": "± 16308781",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 6767,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 7012,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 25481781,
            "range": "± 775147",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 11891979,
            "range": "± 6662",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 18348950,
            "range": "± 306751",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 5095234,
            "range": "± 1221",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 6376743,
            "range": "± 108670",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 16730181,
            "range": "± 40202",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 139364269,
            "range": "± 605733",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 875635117,
            "range": "± 7011837",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 6599797,
            "range": "± 55718",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 8028415,
            "range": "± 30416",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 30381947,
            "range": "± 709452",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 269859253,
            "range": "± 3264346",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 6939409,
            "range": "± 59029",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 352995,
            "range": "± 1733",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 949107451,
            "range": "± 2222547",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 88811,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 171490,
            "range": "± 4021",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 225688,
            "range": "± 5600",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 63441,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 63438,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 127540,
            "range": "± 67",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 148686,
            "range": "± 47",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 190922,
            "range": "± 67",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 75051,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 75061,
            "range": "± 55",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 150419,
            "range": "± 83",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 150229,
            "range": "± 59",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 188237,
            "range": "± 64",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 168002,
            "range": "± 38",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 168005,
            "range": "± 70",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 252350,
            "range": "± 109",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 252366,
            "range": "± 64",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 252304,
            "range": "± 112",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 3440815,
            "range": "± 9156",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 5195927,
            "range": "± 3634",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 22420481,
            "range": "± 3344",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 104603730,
            "range": "± 2879508",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1209946645,
            "range": "± 5206036",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 10263463783,
            "range": "± 21775329",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 3341608,
            "range": "± 1139",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 5097857,
            "range": "± 1415",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 22332517,
            "range": "± 3904",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 101594304,
            "range": "± 1806407",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1209459040,
            "range": "± 2409602",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 10260025704,
            "range": "± 13368134",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 3342125,
            "range": "± 729",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 5784695,
            "range": "± 842",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 21548395,
            "range": "± 3732",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 103042337,
            "range": "± 2534038",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1209328816,
            "range": "± 4907876",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 10256741683,
            "range": "± 12472596",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 3341154,
            "range": "± 560",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 4690122,
            "range": "± 999",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 25206330,
            "range": "± 5086",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 148035548,
            "range": "± 1493354",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1198789819,
            "range": "± 6209531",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 10261339010,
            "range": "± 36030026",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 3347360,
            "range": "± 1589",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 4801171,
            "range": "± 2345",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 72330606,
            "range": "± 707535",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 103032625,
            "range": "± 2381013",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1155203873,
            "range": "± 5282429",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 10209973081,
            "range": "± 7996334",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 3539067,
            "range": "± 11602",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 4890816,
            "range": "± 13144",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 20090415,
            "range": "± 28800",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 103010952,
            "range": "± 2896892",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1526205933,
            "range": "± 9789445",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 9742853454,
            "range": "± 13197243",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 6897084,
            "range": "± 937390",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 8490457,
            "range": "± 892300",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 25005427,
            "range": "± 446140",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 112566019,
            "range": "± 3927277",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 906961023,
            "range": "± 8026652",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 11870792378,
            "range": "± 11547594",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 3320934,
            "range": "± 1289",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 33395621,
            "range": "± 7272",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 334047358,
            "range": "± 76215",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 3339270561,
            "range": "± 192790",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 33401097364,
            "range": "± 6003895",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 3337072,
            "range": "± 673",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 33402201,
            "range": "± 6527",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 332464871,
            "range": "± 60366",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 3341034971,
            "range": "± 454639",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 33427933411,
            "range": "± 4099995",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 3338699,
            "range": "± 1521",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 33441975,
            "range": "± 5914",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 334337280,
            "range": "± 36267",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 3344599582,
            "range": "± 4520249",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 33423518591,
            "range": "± 3262690",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 3348590,
            "range": "± 824",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 33462017,
            "range": "± 15040",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 334998038,
            "range": "± 81169",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 3347492100,
            "range": "± 778363",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 33487928516,
            "range": "± 2460335",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 3492456,
            "range": "± 15405",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 34678256,
            "range": "± 14578",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 346575118,
            "range": "± 60528",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 3471377535,
            "range": "± 757632",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 34734949337,
            "range": "± 12825663",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 5780967,
            "range": "± 546619",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 43328337,
            "range": "± 560532",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 432014102,
            "range": "± 4841883",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 4264421101,
            "range": "± 28912436",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 42759243563,
            "range": "± 61595759",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3324722,
            "range": "± 3010",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3323086,
            "range": "± 1418",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 3325181,
            "range": "± 979",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 3324298,
            "range": "± 1854",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 3326287,
            "range": "± 1258",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 3322452,
            "range": "± 4302",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 4672577,
            "range": "± 827",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 4670007,
            "range": "± 904",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 4670935,
            "range": "± 803",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 4670624,
            "range": "± 997",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 3324839,
            "range": "± 1350",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 4872399,
            "range": "± 1201",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 19820742,
            "range": "± 7455",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 19823452,
            "range": "± 16683",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 19824833,
            "range": "± 11578",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 3321846,
            "range": "± 948",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 4867519,
            "range": "± 1096",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 19809663,
            "range": "± 10972",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 102519412,
            "range": "± 2642168",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 104596956,
            "range": "± 2885069",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 3339736,
            "range": "± 4201",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 4703389,
            "range": "± 10872",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 21736569,
            "range": "± 57046",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 111774804,
            "range": "± 1100945",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8660",
            "value": 861433825,
            "range": "± 3947240",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 3522465,
            "range": "± 58556",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 6739119,
            "range": "± 68014",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 40800052,
            "range": "± 170211",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 212137206,
            "range": "± 1114257",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 1966941157,
            "range": "± 5217687",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 3318156,
            "range": "± 1485",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 3318006,
            "range": "± 1370",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3320273,
            "range": "± 1959",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3322730,
            "range": "± 1160",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3308973,
            "range": "± 4128",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 3322325,
            "range": "± 267",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 3324714,
            "range": "± 11994",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3324304,
            "range": "± 567",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3323543,
            "range": "± 867",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 3319565,
            "range": "± 1157",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 3319073,
            "range": "± 14368",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 3317316,
            "range": "± 1565",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 3322315,
            "range": "± 1971",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 3325659,
            "range": "± 1379",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3320974,
            "range": "± 1192",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 3321531,
            "range": "± 1604",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 3322173,
            "range": "± 1143",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 3324884,
            "range": "± 1249",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 3328354,
            "range": "± 1477",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 3323637,
            "range": "± 1126",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 3332538,
            "range": "± 3238",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 3325044,
            "range": "± 929",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 3347112,
            "range": "± 4251",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 3323477,
            "range": "± 1101",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 3383375,
            "range": "± 5584",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3325086,
            "range": "± 1046",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 3477917,
            "range": "± 20273",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3329488,
            "range": "± 2901",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 3663937,
            "range": "± 61182",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 3332496,
            "range": "± 6350",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4190887,
            "range": "± 202616",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 3348228,
            "range": "± 21436",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 158044,
            "range": "± 2917",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 174979,
            "range": "± 1198",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 942,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 684,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 438,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 74494,
            "range": "± 76",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1528318,
            "range": "± 9069",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 412906,
            "range": "± 3423",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 3589,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 2555,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1615,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 14,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 58,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 11,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 53,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 10937,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 66602,
            "range": "± 55",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 35,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 66,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 205,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 121,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 5322,
            "range": "± 23",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 139,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 3708,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 20692,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 21,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 11,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 215,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 17,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 172,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 11691,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 109461,
            "range": "± 3317",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 3,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 31,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 29,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 5675,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 28493,
            "range": "± 28",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 20,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 32,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 493954,
            "range": "± 721",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 990009,
            "range": "± 734",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 1708241,
            "range": "± 1546",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_bytes_le",
            "value": 27940,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Block::serialize (bincode)",
            "value": 57641,
            "range": "± 75",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_string (serde_json)",
            "value": 211117,
            "range": "± 43",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_bytes_le",
            "value": 19656229,
            "range": "± 36286",
            "unit": "ns/iter"
          },
          {
            "name": "Block::deserialize (bincode)",
            "value": 19518069,
            "range": "± 41282",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_str (serde_json)",
            "value": 20207484,
            "range": "± 29818",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_bytes_le",
            "value": 373,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::serialize (bincode)",
            "value": 788,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_string (serde_json)",
            "value": 2493,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_bytes_le",
            "value": 193,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::deserialize (bincode)",
            "value": 317,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_str (serde_json)",
            "value": 14322,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_bytes_le",
            "value": 27983,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::serialize (bincode)",
            "value": 58213,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_string (serde_json)",
            "value": 200709,
            "range": "± 129",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_bytes_le",
            "value": 16910423,
            "range": "± 58308",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::deserialize (bincode)",
            "value": 16867095,
            "range": "± 51046",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_str (serde_json)",
            "value": 17489527,
            "range": "± 25758",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_bytes_le",
            "value": 7377,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::serialize (bincode)",
            "value": 15166,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_string (serde_json)",
            "value": 47689,
            "range": "± 169",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_bytes_le",
            "value": 4247005,
            "range": "± 26028",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::deserialize (bincode)",
            "value": 4243460,
            "range": "± 7472",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_str (serde_json)",
            "value": 4389871,
            "range": "± 9281",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_bytes_le",
            "value": 6832,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::serialize (bincode)",
            "value": 13800,
            "range": "± 25",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_string (serde_json)",
            "value": 43853,
            "range": "± 59",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_bytes_le",
            "value": 3544031,
            "range": "± 17619",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::deserialize (bincode)",
            "value": 3544276,
            "range": "± 3412",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_str (serde_json)",
            "value": 3675581,
            "range": "± 10092",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - deploy",
            "value": 60886292334,
            "range": "± 96558824",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - deployment",
            "value": 457609323,
            "range": "± 2675055",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - execution (transfer)",
            "value": 42258217448,
            "range": "± 191725544",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - execution (transfer)",
            "value": 48974316,
            "range": "± 242418",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 7109177838,
            "range": "± 86872930",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 272603908,
            "range": "± 1110255",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 238975184,
            "range": "± 894003",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1178262656,
            "range": "± 5313238",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "735222fd1b61e1038145c1704cd1cbb4c6242a80",
          "message": "Merge pull request #1540 from AleoHQ/feat/ed25519\n\nAdds method `to_ed25519` on Aleo private key",
          "timestamp": "2023-05-31T14:48:33-07:00",
          "tree_id": "ac7cda3e7d75115bfaa1dd63617ca55706adb421",
          "url": "https://github.com/AleoHQ/snarkVM/commit/735222fd1b61e1038145c1704cd1cbb4c6242a80"
        },
        "date": 1685584795923,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 104085691,
            "range": "± 7544696",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 695065692,
            "range": "± 1883337",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1283355278,
            "range": "± 25713534",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 1986513207,
            "range": "± 80311475",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2514233708,
            "range": "± 5924600",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 2790484758,
            "range": "± 7619813",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 5137097575,
            "range": "± 10045105",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 9250636569,
            "range": "± 9600124",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 70753559,
            "range": "± 296089",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 500029976,
            "range": "± 883704",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 4283963309,
            "range": "± 13764132",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 90783,
            "range": "± 145",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 227299,
            "range": "± 121",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1632245227,
            "range": "± 6072019",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 97492514,
            "range": "± 526617",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 610147995,
            "range": "± 4014270",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 10104973333,
            "range": "± 13924514",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 7471,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 7610,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 29991962,
            "range": "± 402000",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 13779648,
            "range": "± 7360",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 22072553,
            "range": "± 786992",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 5907074,
            "range": "± 8005",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 7182010,
            "range": "± 25639",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 19025633,
            "range": "± 70633",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 157153582,
            "range": "± 2830577",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 931909803,
            "range": "± 2128051",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 7329185,
            "range": "± 16243",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 9024182,
            "range": "± 23233",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 31871761,
            "range": "± 926370",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 237169530,
            "range": "± 6569475",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 8024633,
            "range": "± 5647",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 349807,
            "range": "± 838",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 737648535,
            "range": "± 1227086",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 97397,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 191651,
            "range": "± 4109",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 246960,
            "range": "± 6434",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 70034,
            "range": "± 48",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 69988,
            "range": "± 60",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 140470,
            "range": "± 72",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 163798,
            "range": "± 71",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 210493,
            "range": "± 134",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 79009,
            "range": "± 33",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 78947,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 158850,
            "range": "± 295",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 158731,
            "range": "± 61",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 198398,
            "range": "± 62",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 173280,
            "range": "± 49",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 173167,
            "range": "± 25",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 260881,
            "range": "± 74",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 260914,
            "range": "± 116",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 260912,
            "range": "± 52",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 3945984,
            "range": "± 3275",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 5983785,
            "range": "± 1821",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 25943742,
            "range": "± 5200",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 118967817,
            "range": "± 2352968",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1393574314,
            "range": "± 3759325",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 11870130302,
            "range": "± 10540453",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 3834840,
            "range": "± 3220",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 5869666,
            "range": "± 4128",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 25838914,
            "range": "± 3794",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 117886712,
            "range": "± 1934020",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1396973085,
            "range": "± 4931513",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 11881561335,
            "range": "± 32666674",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 3828425,
            "range": "± 1812",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 6662868,
            "range": "± 2320",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 24933653,
            "range": "± 4033",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 117587600,
            "range": "± 1970660",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1391486456,
            "range": "± 7173804",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 11885568155,
            "range": "± 14048761",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 3828229,
            "range": "± 2447",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 5389444,
            "range": "± 3144",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 29105255,
            "range": "± 8603",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 166677401,
            "range": "± 3686552",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1391790372,
            "range": "± 4646938",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 11873735137,
            "range": "± 19886040",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 3834428,
            "range": "± 5720",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 5513437,
            "range": "± 3663",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 79487198,
            "range": "± 1125675",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 119390438,
            "range": "± 1918189",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1331187021,
            "range": "± 4626895",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 11821190372,
            "range": "± 21580740",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 3978773,
            "range": "± 11484",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 5547949,
            "range": "± 14394",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 23189027,
            "range": "± 24968",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 117343241,
            "range": "± 2365900",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1762480497,
            "range": "± 3430937",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 11280649753,
            "range": "± 9335843",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 5678343,
            "range": "± 347334",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 7375951,
            "range": "± 366864",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 26014592,
            "range": "± 356754",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 117345830,
            "range": "± 445512",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 1029574456,
            "range": "± 2404362",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 13719102185,
            "range": "± 6413875",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 3984798,
            "range": "± 4090",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 40192959,
            "range": "± 733031",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 386860830,
            "range": "± 29336",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 3868664456,
            "range": "± 257947",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 38691836905,
            "range": "± 1297447",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 3976396,
            "range": "± 1393",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 40226395,
            "range": "± 735317",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 387031440,
            "range": "± 69507",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 3869563408,
            "range": "± 813835",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 38689698155,
            "range": "± 864257",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 3979906,
            "range": "± 3067",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 40265729,
            "range": "± 747147",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 387058975,
            "range": "± 63464",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 3869812679,
            "range": "± 177137",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 38717911229,
            "range": "± 2728101",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 3989010,
            "range": "± 1679",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 40270518,
            "range": "± 749060",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 387360903,
            "range": "± 41092",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 3871712619,
            "range": "± 119580",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 38737463945,
            "range": "± 6452582",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 4128606,
            "range": "± 10643",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 41582650,
            "range": "± 752315",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 400216137,
            "range": "± 68924",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 4001701556,
            "range": "± 659376",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 40015506551,
            "range": "± 1928638",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 5345822,
            "range": "± 177686",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 48120227,
            "range": "± 397444",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 477894932,
            "range": "± 572905",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 4779983358,
            "range": "± 1563021",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 47785809181,
            "range": "± 4647800",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3816091,
            "range": "± 4135",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3814682,
            "range": "± 2178",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 3812582,
            "range": "± 1697",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 3815125,
            "range": "± 2206",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 3815104,
            "range": "± 1913",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 3836755,
            "range": "± 1973",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 5432427,
            "range": "± 4355",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 5436177,
            "range": "± 2828",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 5431830,
            "range": "± 2851",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 5435562,
            "range": "± 8313",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 3851049,
            "range": "± 1893",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 5695361,
            "range": "± 2229",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 23508419,
            "range": "± 227518",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 23508391,
            "range": "± 228155",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 23511706,
            "range": "± 234462",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 3869000,
            "range": "± 2916",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 5709701,
            "range": "± 1560",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 23522813,
            "range": "± 233119",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 119946982,
            "range": "± 2123717",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 120318105,
            "range": "± 2066521",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 3906283,
            "range": "± 5114",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 5626974,
            "range": "± 9296",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 26334109,
            "range": "± 301275",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 129780953,
            "range": "± 1719635",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8627",
            "value": 1002272570,
            "range": "± 3272208",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 4039561,
            "range": "± 42026",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 8764524,
            "range": "± 102624",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 48082910,
            "range": "± 745365",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 243974958,
            "range": "± 1080064",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 2265737277,
            "range": "± 3759633",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 3989749,
            "range": "± 1552",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 4513468,
            "range": "± 2575",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3991604,
            "range": "± 2141",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 4487786,
            "range": "± 2800",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3991214,
            "range": "± 1673",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 4468589,
            "range": "± 2356",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 3991068,
            "range": "± 2273",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 4442480,
            "range": "± 2971",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3989929,
            "range": "± 1634",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 4421096,
            "range": "± 2792",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 3989763,
            "range": "± 2320",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 4399508,
            "range": "± 1688",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 3988541,
            "range": "± 3225",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 4378737,
            "range": "± 3349",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3994407,
            "range": "± 2784",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 4356025,
            "range": "± 4338",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 3995110,
            "range": "± 2355",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 4336734,
            "range": "± 3114",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 3995369,
            "range": "± 2999",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 4311831,
            "range": "± 2472",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 4002215,
            "range": "± 2664",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 4289884,
            "range": "± 4275",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 4008745,
            "range": "± 3573",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 4266425,
            "range": "± 3364",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 4049134,
            "range": "± 4066",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 4246481,
            "range": "± 2288",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 4136988,
            "range": "± 11933",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 4225019,
            "range": "± 4492",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 4259096,
            "range": "± 18459",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 4204331,
            "range": "± 5319",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4484395,
            "range": "± 57316",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 4180738,
            "range": "± 18390",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 186902,
            "range": "± 3963",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 197060,
            "range": "± 1100",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 1064,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 746,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 461,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 87073,
            "range": "± 56",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1765645,
            "range": "± 11195",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 472917,
            "range": "± 4635",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 4138,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 2938,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1797,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 9,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 67,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 14,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 63,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 12675,
            "range": "± 36",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 79084,
            "range": "± 79",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 41,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 75,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 207,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 77,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 6196,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 130,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 4315,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 23218,
            "range": "± 30",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 18,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 235,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 17,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 157,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 12663,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 125482,
            "range": "± 6726",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 36,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 34,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6371,
            "range": "± 42",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 33777,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 20,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 37,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 579351,
            "range": "± 671",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 1156089,
            "range": "± 953",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 1996965,
            "range": "± 1808",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_bytes_le",
            "value": 30279,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "Block::serialize (bincode)",
            "value": 64973,
            "range": "± 65",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_string (serde_json)",
            "value": 220210,
            "range": "± 182",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_bytes_le",
            "value": 22407255,
            "range": "± 108216",
            "unit": "ns/iter"
          },
          {
            "name": "Block::deserialize (bincode)",
            "value": 22455414,
            "range": "± 20599",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_str (serde_json)",
            "value": 23153462,
            "range": "± 32386",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_bytes_le",
            "value": 362,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::serialize (bincode)",
            "value": 748,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_string (serde_json)",
            "value": 2442,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_bytes_le",
            "value": 227,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::deserialize (bincode)",
            "value": 361,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_str (serde_json)",
            "value": 14848,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_bytes_le",
            "value": 32365,
            "range": "± 64",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::serialize (bincode)",
            "value": 64354,
            "range": "± 84",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_string (serde_json)",
            "value": 210105,
            "range": "± 253",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_bytes_le",
            "value": 19372092,
            "range": "± 31268",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::deserialize (bincode)",
            "value": 19273667,
            "range": "± 8550",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_str (serde_json)",
            "value": 19923474,
            "range": "± 51808",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_bytes_le",
            "value": 8038,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::serialize (bincode)",
            "value": 16278,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_string (serde_json)",
            "value": 46965,
            "range": "± 79",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_bytes_le",
            "value": 4861470,
            "range": "± 10017",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::deserialize (bincode)",
            "value": 4975770,
            "range": "± 18472",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_str (serde_json)",
            "value": 5009089,
            "range": "± 23395",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_bytes_le",
            "value": 7306,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::serialize (bincode)",
            "value": 14838,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_string (serde_json)",
            "value": 43770,
            "range": "± 46",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_bytes_le",
            "value": 4038052,
            "range": "± 4938",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::deserialize (bincode)",
            "value": 4168962,
            "range": "± 6395",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_str (serde_json)",
            "value": 4171600,
            "range": "± 3306",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - deploy",
            "value": 64571217776,
            "range": "± 111765299",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - deployment",
            "value": 427013217,
            "range": "± 2878628",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - execution (transfer)",
            "value": 43477546261,
            "range": "± 173904010",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - execution (transfer)",
            "value": 55021000,
            "range": "± 137686",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 8307021298,
            "range": "± 9693950",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 312286075,
            "range": "± 232703",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 276848599,
            "range": "± 495326",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1390665703,
            "range": "± 5486848",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "distinct": true,
          "id": "8e406fc29fdbebbbee2008678177892bb5ad9922",
          "message": "chore(snarkvm): bump version for new release",
          "timestamp": "2023-05-31T14:50:27-07:00",
          "tree_id": "bd9a895ae1fd325b702051b041ccab8aa0cc153d",
          "url": "https://github.com/AleoHQ/snarkVM/commit/8e406fc29fdbebbbee2008678177892bb5ad9922"
        },
        "date": 1685586101953,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 112567758,
            "range": "± 6754429",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 784965720,
            "range": "± 12877814",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1463169394,
            "range": "± 20438750",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 2149845819,
            "range": "± 28832364",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2836515845,
            "range": "± 17346462",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 3155548519,
            "range": "± 40794498",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 5587196086,
            "range": "± 99264592",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 10026611296,
            "range": "± 118827731",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 75016310,
            "range": "± 1213075",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 551703639,
            "range": "± 9843453",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 4999959305,
            "range": "± 143537006",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 96730,
            "range": "± 2876",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 242135,
            "range": "± 115",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1781821300,
            "range": "± 12303133",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 106870850,
            "range": "± 2279024",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 666412073,
            "range": "± 9050556",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 10826021788,
            "range": "± 170527874",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 8445,
            "range": "± 119",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 8815,
            "range": "± 110",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 31878710,
            "range": "± 1189383",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 14797027,
            "range": "± 217936",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 23282676,
            "range": "± 1241369",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 6356716,
            "range": "± 104999",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 7925685,
            "range": "± 185386",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 20705231,
            "range": "± 234476",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 170517720,
            "range": "± 3702831",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 1033636267,
            "range": "± 17809260",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 8348765,
            "range": "± 384281",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 10346182,
            "range": "± 221555",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 37408019,
            "range": "± 595346",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 266684323,
            "range": "± 7009295",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 8301796,
            "range": "± 8269",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 402718,
            "range": "± 827",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 864793318,
            "range": "± 707629",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 111339,
            "range": "± 2557",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 216211,
            "range": "± 5355",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 283567,
            "range": "± 11305",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 78718,
            "range": "± 1307",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 77117,
            "range": "± 21",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 156972,
            "range": "± 6280",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 185585,
            "range": "± 5816",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 237292,
            "range": "± 8086",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 93924,
            "range": "± 5018",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 92418,
            "range": "± 3043",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 185530,
            "range": "± 5603",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 185092,
            "range": "± 18987",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 230887,
            "range": "± 9819",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 202393,
            "range": "± 89",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 201944,
            "range": "± 72",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 312723,
            "range": "± 7396",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 315513,
            "range": "± 8377",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 305813,
            "range": "± 79",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 4112894,
            "range": "± 21077",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 6239894,
            "range": "± 1957",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 26794437,
            "range": "± 4745",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 128166434,
            "range": "± 2652421",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1510869768,
            "range": "± 21791919",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 12701710681,
            "range": "± 162465341",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 4121621,
            "range": "± 61386",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 6312227,
            "range": "± 71785",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 27623586,
            "range": "± 381585",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 127024200,
            "range": "± 4080066",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1493906734,
            "range": "± 27519219",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 12841480969,
            "range": "± 120749995",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 4008290,
            "range": "± 753",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 6938108,
            "range": "± 1506",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 26773405,
            "range": "± 578785",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 127175262,
            "range": "± 2238884",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1543637917,
            "range": "± 18747061",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 12835319356,
            "range": "± 98991802",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 4013557,
            "range": "± 1618",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 5879596,
            "range": "± 142322",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 31792260,
            "range": "± 653887",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 181499557,
            "range": "± 2627325",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1495303311,
            "range": "± 22680937",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 12810391878,
            "range": "± 79813068",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 4017827,
            "range": "± 1991",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 5733011,
            "range": "± 1383",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 85010259,
            "range": "± 1664202",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 129313174,
            "range": "± 2914718",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1448214787,
            "range": "± 21291624",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 12726221937,
            "range": "± 137016143",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 4422832,
            "range": "± 93600",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 5850387,
            "range": "± 18959",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 24142197,
            "range": "± 50499",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 126465104,
            "range": "± 4742014",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1890610183,
            "range": "± 19674592",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 12147410900,
            "range": "± 62458643",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 6645932,
            "range": "± 874484",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 8390970,
            "range": "± 1140483",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 29078552,
            "range": "± 996478",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 130411325,
            "range": "± 2382740",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 1115934034,
            "range": "± 19417208",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 14669465870,
            "range": "± 207137352",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 4143068,
            "range": "± 67298",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 41448861,
            "range": "± 489556",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 417146261,
            "range": "± 4071629",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 4182615139,
            "range": "± 49099935",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 40117172405,
            "range": "± 14076727",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 4010651,
            "range": "± 1125",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 40134426,
            "range": "± 7861",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 417728763,
            "range": "± 9421286",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 4012989989,
            "range": "± 78416818",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 40133049132,
            "range": "± 422020966",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 4010788,
            "range": "± 1768",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 40133617,
            "range": "± 4657",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 401292497,
            "range": "± 53818",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 4013090029,
            "range": "± 23973958",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 40476014415,
            "range": "± 870415362",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 4181759,
            "range": "± 51159",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 41488175,
            "range": "± 767970",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 416951172,
            "range": "± 2768708",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 4196806873,
            "range": "± 31831487",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 40145451991,
            "range": "± 19478727",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 4346855,
            "range": "± 61335",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 41683392,
            "range": "± 43870",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 428008762,
            "range": "± 2792880",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 4166641765,
            "range": "± 52993670",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 41633813240,
            "range": "± 10278219",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 5869031,
            "range": "± 245401",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 53953920,
            "range": "± 1777414",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 533524098,
            "range": "± 13337947",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 5054158254,
            "range": "± 64606556",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 50980409333,
            "range": "± 627451348",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3992695,
            "range": "± 1522",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3991483,
            "range": "± 1552",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 4156547,
            "range": "± 45025",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 4174470,
            "range": "± 71813",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 4095334,
            "range": "± 52017",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 4186981,
            "range": "± 75302",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 5817628,
            "range": "± 114230",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 5812302,
            "range": "± 57693",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 5804064,
            "range": "± 119656",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 5774486,
            "range": "± 77500",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 4142779,
            "range": "± 45156",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 6073992,
            "range": "± 91937",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 24456802,
            "range": "± 191233",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 24849027,
            "range": "± 426057",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 24480265,
            "range": "± 968086",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 4118819,
            "range": "± 76038",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 5819207,
            "range": "± 1152",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 23792106,
            "range": "± 3475",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 126580637,
            "range": "± 3070356",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 128756022,
            "range": "± 3632436",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 4016855,
            "range": "± 2832",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 5947378,
            "range": "± 110520",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 26868261,
            "range": "± 579329",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 140492448,
            "range": "± 3223442",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8616",
            "value": 1078506943,
            "range": "± 21833542",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 4265091,
            "range": "± 68145",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 7893401,
            "range": "± 165998",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 47855105,
            "range": "± 125374",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 256504804,
            "range": "± 2851658",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 2407087760,
            "range": "± 36838591",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 4116043,
            "range": "± 56680",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 4250317,
            "range": "± 92324",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3970428,
            "range": "± 1016",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3991769,
            "range": "± 1059",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3987408,
            "range": "± 893",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 4094039,
            "range": "± 34563",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 4116205,
            "range": "± 64030",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3988075,
            "range": "± 1211",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3987681,
            "range": "± 602",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 4106365,
            "range": "± 27569",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 4142204,
            "range": "± 54326",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 4168113,
            "range": "± 176735",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 4113804,
            "range": "± 93361",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 4184857,
            "range": "± 64760",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 4101311,
            "range": "± 69991",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 4108165,
            "range": "± 86187",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 4089997,
            "range": "± 41063",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 4123139,
            "range": "± 91486",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 4160790,
            "range": "± 70374",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 4107468,
            "range": "± 95112",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 4141788,
            "range": "± 89038",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 4139263,
            "range": "± 75294",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 4145701,
            "range": "± 30720",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 4101967,
            "range": "± 24196",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 4064160,
            "range": "± 4148",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3994079,
            "range": "± 1295",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 4154693,
            "range": "± 7377",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3993721,
            "range": "± 2861",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 4734218,
            "range": "± 383094",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 4163702,
            "range": "± 85857",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4758157,
            "range": "± 173479",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 4126214,
            "range": "± 63562",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 195988,
            "range": "± 15414",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 215192,
            "range": "± 47950",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 1155,
            "range": "± 49",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 858,
            "range": "± 81",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 548,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 91463,
            "range": "± 7550",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1868367,
            "range": "± 79808",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 508708,
            "range": "± 22334",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 4391,
            "range": "± 208",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 3074,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1976,
            "range": "± 124",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 13,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 17,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 72,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 14,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 65,
            "range": "± 8",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 13308,
            "range": "± 357",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 81589,
            "range": "± 2154",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 43,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 82,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 257,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 152,
            "range": "± 19",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 6388,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 167,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 4434,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 24993,
            "range": "± 21",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 25,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 263,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 21,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 215,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 14383,
            "range": "± 594",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 137285,
            "range": "± 10094",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 38,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 36,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6943,
            "range": "± 272",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 34827,
            "range": "± 1093",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 24,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 41,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 604423,
            "range": "± 20198",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 1196582,
            "range": "± 1434",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 2092338,
            "range": "± 77821",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_bytes_le",
            "value": 35935,
            "range": "± 541",
            "unit": "ns/iter"
          },
          {
            "name": "Block::serialize (bincode)",
            "value": 71431,
            "range": "± 1736",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_string (serde_json)",
            "value": 261426,
            "range": "± 2563",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_bytes_le",
            "value": 24899255,
            "range": "± 793268",
            "unit": "ns/iter"
          },
          {
            "name": "Block::deserialize (bincode)",
            "value": 24909308,
            "range": "± 308533",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_str (serde_json)",
            "value": 25201593,
            "range": "± 388497",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_bytes_le",
            "value": 458,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Header::serialize (bincode)",
            "value": 949,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_string (serde_json)",
            "value": 3054,
            "range": "± 71",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_bytes_le",
            "value": 242,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "Header::deserialize (bincode)",
            "value": 396,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_str (serde_json)",
            "value": 17470,
            "range": "± 153",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_bytes_le",
            "value": 34498,
            "range": "± 313",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::serialize (bincode)",
            "value": 70825,
            "range": "± 34",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_string (serde_json)",
            "value": 247603,
            "range": "± 4575",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_bytes_le",
            "value": 21101581,
            "range": "± 311547",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::deserialize (bincode)",
            "value": 21116748,
            "range": "± 316374",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_str (serde_json)",
            "value": 21960594,
            "range": "± 986170",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_bytes_le",
            "value": 8829,
            "range": "± 197",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::serialize (bincode)",
            "value": 17898,
            "range": "± 392",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_string (serde_json)",
            "value": 59654,
            "range": "± 906",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_bytes_le",
            "value": 5086822,
            "range": "± 49119",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::deserialize (bincode)",
            "value": 5302155,
            "range": "± 247004",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_str (serde_json)",
            "value": 5478596,
            "range": "± 53051",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_bytes_le",
            "value": 8088,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::serialize (bincode)",
            "value": 16533,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_string (serde_json)",
            "value": 53104,
            "range": "± 1336",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_bytes_le",
            "value": 4419689,
            "range": "± 62874",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::deserialize (bincode)",
            "value": 4418945,
            "range": "± 83505",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_str (serde_json)",
            "value": 4570243,
            "range": "± 58903",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - deploy",
            "value": 73022646587,
            "range": "± 540265878",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - deployment",
            "value": 513840548,
            "range": "± 15658216",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - execution (transfer)",
            "value": 49209629464,
            "range": "± 429411642",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - execution (transfer)",
            "value": 60868211,
            "range": "± 3814719",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 8952914548,
            "range": "± 93058501",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 341192627,
            "range": "± 6174015",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 303957686,
            "range": "± 5493311",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1467170236,
            "range": "± 49782230",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "34e308390a987034f7133a304941cc9ba606c8fb",
          "message": "Merge pull request #1613 from AleoHQ/refactor/transition\n\nAdds `Transition::is_coinbase` and `Transition::is_split`",
          "timestamp": "2023-06-01T10:07:10-07:00",
          "tree_id": "d4689f074989d571e49e1fed4da7881fc6c1fcfd",
          "url": "https://github.com/AleoHQ/snarkVM/commit/34e308390a987034f7133a304941cc9ba606c8fb"
        },
        "date": 1685653945427,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 106538236,
            "range": "± 23272701",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 750463895,
            "range": "± 53438284",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1264683146,
            "range": "± 18450860",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 1972274354,
            "range": "± 59014850",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2433052444,
            "range": "± 25793172",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 2784513620,
            "range": "± 40343988",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 4985529023,
            "range": "± 75527441",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 9313533527,
            "range": "± 171557810",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 66992594,
            "range": "± 2441750",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 509801491,
            "range": "± 17344445",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 4345337416,
            "range": "± 118011126",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 82882,
            "range": "± 5298",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 206627,
            "range": "± 12454",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1544058458,
            "range": "± 27788922",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 97753302,
            "range": "± 4698906",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 589848628,
            "range": "± 21300385",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 9483513689,
            "range": "± 241283774",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 7244,
            "range": "± 429",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 7594,
            "range": "± 205",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 28343221,
            "range": "± 1694188",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 11880174,
            "range": "± 434537",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 20773424,
            "range": "± 1232306",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 5240201,
            "range": "± 197429",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 7294846,
            "range": "± 263209",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 18198154,
            "range": "± 636836",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 155338980,
            "range": "± 6978603",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 908160480,
            "range": "± 32007109",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 6982582,
            "range": "± 256297",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 8529755,
            "range": "± 235316",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 31385655,
            "range": "± 1559446",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 230980956,
            "range": "± 5083086",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 7361224,
            "range": "± 174826",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 374739,
            "range": "± 8407",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 780382560,
            "range": "± 21167990",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 91934,
            "range": "± 3833",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 182942,
            "range": "± 5927",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 231089,
            "range": "± 17086",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 70397,
            "range": "± 3252",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 65551,
            "range": "± 4598",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 132728,
            "range": "± 5819",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 155835,
            "range": "± 11519",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 206180,
            "range": "± 12805",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 76714,
            "range": "± 4110",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 80659,
            "range": "± 4226",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 153702,
            "range": "± 5818",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 160882,
            "range": "± 8670",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 196122,
            "range": "± 12265",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 187674,
            "range": "± 12210",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 168161,
            "range": "± 5663",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 257428,
            "range": "± 12913",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 274836,
            "range": "± 13961",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 275325,
            "range": "± 12555",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 3954256,
            "range": "± 89129",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 5804833,
            "range": "± 117984",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 24124923,
            "range": "± 849760",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 112262920,
            "range": "± 4468037",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1363288756,
            "range": "± 33780874",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 11019877446,
            "range": "± 285363984",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 3398885,
            "range": "± 237192",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 5319855,
            "range": "± 181348",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 22949693,
            "range": "± 684671",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 112013118,
            "range": "± 4505589",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1289671750,
            "range": "± 50091986",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 11232185660,
            "range": "± 164181880",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 3472134,
            "range": "± 101340",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 6451419,
            "range": "± 143984",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 23754221,
            "range": "± 644246",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 106617912,
            "range": "± 3310601",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1283593084,
            "range": "± 21887572",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 11203967854,
            "range": "± 214332944",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 3607764,
            "range": "± 168525",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 5102625,
            "range": "± 217997",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 27841789,
            "range": "± 1120489",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 157897775,
            "range": "± 6343419",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1386898564,
            "range": "± 34198924",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 11369236766,
            "range": "± 238670100",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 3498401,
            "range": "± 97684",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 4899715,
            "range": "± 129835",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 76612035,
            "range": "± 1077899",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 113615404,
            "range": "± 1310706",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1235213040,
            "range": "± 33007639",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 11020038732,
            "range": "± 141774980",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 3611318,
            "range": "± 54765",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 5106769,
            "range": "± 123125",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 20498228,
            "range": "± 332271",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 111875490,
            "range": "± 4786649",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1642667232,
            "range": "± 38699095",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 10527833826,
            "range": "± 110270438",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 5911056,
            "range": "± 559751",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 7664456,
            "range": "± 880239",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 25112293,
            "range": "± 867004",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 113928111,
            "range": "± 7332347",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 1064110968,
            "range": "± 16097279",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 13040988708,
            "range": "± 256715485",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 3396272,
            "range": "± 95283",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 34202361,
            "range": "± 1723619",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 361958208,
            "range": "± 15686661",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 3545309488,
            "range": "± 113956093",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 35253123550,
            "range": "± 960054448",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 3383267,
            "range": "± 139659",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 34602471,
            "range": "± 1026125",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 353609635,
            "range": "± 9680481",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 3552327257,
            "range": "± 104076388",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 34936478144,
            "range": "± 332202716",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 3528244,
            "range": "± 174527",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 36198934,
            "range": "± 929467",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 344886288,
            "range": "± 5959976",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 3533456497,
            "range": "± 157786056",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 35974265683,
            "range": "± 1476438477",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 3443379,
            "range": "± 171299",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 35194642,
            "range": "± 1467297",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 360740322,
            "range": "± 13777625",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 3446854483,
            "range": "± 127811257",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 34950717251,
            "range": "± 1316631866",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 3891985,
            "range": "± 166053",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 37826698,
            "range": "± 1251345",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 359684728,
            "range": "± 7392407",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 3542018621,
            "range": "± 35869144",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 36372702842,
            "range": "± 1587205213",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 5336808,
            "range": "± 315280",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 44213711,
            "range": "± 2738753",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 426555680,
            "range": "± 6137841",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 4379788300,
            "range": "± 60603407",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 44188870513,
            "range": "± 815496212",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3493476,
            "range": "± 183326",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3424796,
            "range": "± 102086",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 3506663,
            "range": "± 124702",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 3783121,
            "range": "± 192325",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 3610036,
            "range": "± 114058",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 3704137,
            "range": "± 109485",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 5194728,
            "range": "± 210687",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 4905500,
            "range": "± 389173",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 5336100,
            "range": "± 244475",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 5293292,
            "range": "± 187099",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 3312483,
            "range": "± 84155",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 4827200,
            "range": "± 112546",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 19996004,
            "range": "± 948042",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 20680331,
            "range": "± 1141514",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 21078839,
            "range": "± 906203",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 3310860,
            "range": "± 85111",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 4889901,
            "range": "± 115871",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 21209205,
            "range": "± 336050",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 112046452,
            "range": "± 3681655",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 119108371,
            "range": "± 5006206",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 3449714,
            "range": "± 123609",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 5167341,
            "range": "± 150598",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 23688475,
            "range": "± 557816",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 126315456,
            "range": "± 2683150",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8596",
            "value": 936324041,
            "range": "± 15369042",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 3613481,
            "range": "± 146668",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 7107746,
            "range": "± 314446",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 40550381,
            "range": "± 1206595",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 228731508,
            "range": "± 4723903",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 2100494896,
            "range": "± 42030588",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 3376782,
            "range": "± 50880",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 3457629,
            "range": "± 212556",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3627391,
            "range": "± 122048",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3357076,
            "range": "± 93081",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3499847,
            "range": "± 200266",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 3432082,
            "range": "± 137249",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 3537141,
            "range": "± 128182",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3501592,
            "range": "± 95514",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3347246,
            "range": "± 72069",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 3499170,
            "range": "± 162415",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 3460870,
            "range": "± 115775",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 3649660,
            "range": "± 63248",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 3467309,
            "range": "± 177205",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 3380021,
            "range": "± 152956",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3598231,
            "range": "± 138680",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 3915096,
            "range": "± 99507",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 3519606,
            "range": "± 134205",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 3457733,
            "range": "± 129879",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 3931229,
            "range": "± 143877",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 3481029,
            "range": "± 97237",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 3372914,
            "range": "± 74653",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 3363561,
            "range": "± 127907",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 3520341,
            "range": "± 187238",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 3349673,
            "range": "± 89638",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 3430112,
            "range": "± 117576",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3388445,
            "range": "± 77632",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 3644734,
            "range": "± 121333",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3449774,
            "range": "± 102904",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 3663028,
            "range": "± 127626",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 3506663,
            "range": "± 154435",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4167865,
            "range": "± 272717",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 3530906,
            "range": "± 190576",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 161343,
            "range": "± 9999",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 201131,
            "range": "± 16561",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 978,
            "range": "± 69",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 709,
            "range": "± 49",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 480,
            "range": "± 23",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 76716,
            "range": "± 5506",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1573852,
            "range": "± 102520",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 440670,
            "range": "± 28226",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 3615,
            "range": "± 250",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 2565,
            "range": "± 193",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1641,
            "range": "± 111",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 11,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 15,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 62,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 11,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 54,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 11651,
            "range": "± 996",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 67345,
            "range": "± 4100",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 36,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 72,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 214,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 128,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 5668,
            "range": "± 405",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 145,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 3719,
            "range": "± 268",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 20748,
            "range": "± 1457",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 22,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 230,
            "range": "± 20",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 18,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 179,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 11585,
            "range": "± 1071",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 112592,
            "range": "± 9725",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 3,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 8,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 8,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 31,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 34,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6217,
            "range": "± 442",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 30335,
            "range": "± 2046",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 22,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 34,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 494180,
            "range": "± 41148",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 985385,
            "range": "± 71143",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 1754831,
            "range": "± 132378",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_bytes_le",
            "value": 32487,
            "range": "± 722",
            "unit": "ns/iter"
          },
          {
            "name": "Block::serialize (bincode)",
            "value": 59843,
            "range": "± 2363",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_string (serde_json)",
            "value": 222996,
            "range": "± 7732",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_bytes_le",
            "value": 21857530,
            "range": "± 620924",
            "unit": "ns/iter"
          },
          {
            "name": "Block::deserialize (bincode)",
            "value": 20291351,
            "range": "± 490712",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_str (serde_json)",
            "value": 21338258,
            "range": "± 686276",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_bytes_le",
            "value": 397,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "Header::serialize (bincode)",
            "value": 796,
            "range": "± 46",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_string (serde_json)",
            "value": 2459,
            "range": "± 88",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_bytes_le",
            "value": 207,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Header::deserialize (bincode)",
            "value": 345,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_str (serde_json)",
            "value": 14462,
            "range": "± 333",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_bytes_le",
            "value": 28079,
            "range": "± 837",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::serialize (bincode)",
            "value": 57413,
            "range": "± 1455",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_string (serde_json)",
            "value": 202660,
            "range": "± 3333",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_bytes_le",
            "value": 17792017,
            "range": "± 398280",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::deserialize (bincode)",
            "value": 17598959,
            "range": "± 446534",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_str (serde_json)",
            "value": 18544729,
            "range": "± 422400",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_bytes_le",
            "value": 7260,
            "range": "± 223",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::serialize (bincode)",
            "value": 15474,
            "range": "± 732",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_string (serde_json)",
            "value": 50323,
            "range": "± 1270",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_bytes_le",
            "value": 4473926,
            "range": "± 148276",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::deserialize (bincode)",
            "value": 4442686,
            "range": "± 141232",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_str (serde_json)",
            "value": 4574333,
            "range": "± 153784",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_bytes_le",
            "value": 7072,
            "range": "± 163",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::serialize (bincode)",
            "value": 14082,
            "range": "± 565",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_string (serde_json)",
            "value": 45181,
            "range": "± 1075",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_bytes_le",
            "value": 3805276,
            "range": "± 118657",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::deserialize (bincode)",
            "value": 3747497,
            "range": "± 174833",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_str (serde_json)",
            "value": 3907837,
            "range": "± 136144",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - deploy",
            "value": 64875648480,
            "range": "± 1076598992",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - deployment",
            "value": 481611963,
            "range": "± 14606632",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - execution (transfer)",
            "value": 44243976172,
            "range": "± 1085984500",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - execution (transfer)",
            "value": 52330922,
            "range": "± 3864817",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 7677682776,
            "range": "± 170890430",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 296374309,
            "range": "± 13875890",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 271546506,
            "range": "± 9572718",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1240493590,
            "range": "± 25334016",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "distinct": true,
          "id": "6142d44836d62cb3bf582cfab6fdd43ee3c25542",
          "message": "chore(snarkvm): bump version for new release",
          "timestamp": "2023-06-01T10:10:39-07:00",
          "tree_id": "579b52234e9af47643dbed82bdeec81a534f1df9",
          "url": "https://github.com/AleoHQ/snarkVM/commit/6142d44836d62cb3bf582cfab6fdd43ee3c25542"
        },
        "date": 1685654753298,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 104477227,
            "range": "± 306059",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 710753457,
            "range": "± 7826302",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1305434288,
            "range": "± 22811345",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 2014146736,
            "range": "± 3508793",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2542550955,
            "range": "± 12538807",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 2821392225,
            "range": "± 9927033",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 5188171901,
            "range": "± 14797698",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 9308876579,
            "range": "± 12125188",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 70543988,
            "range": "± 229950",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 500265716,
            "range": "± 1203050",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 4805842716,
            "range": "± 94783309",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 91356,
            "range": "± 46",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 228472,
            "range": "± 1484",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1639735971,
            "range": "± 3944188",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 98925466,
            "range": "± 1207749",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 615625562,
            "range": "± 1471769",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 10167931487,
            "range": "± 27797857",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 7679,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 7740,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 29900155,
            "range": "± 551386",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 13823954,
            "range": "± 6621",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 22403462,
            "range": "± 288663",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 5925817,
            "range": "± 8671",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 7314663,
            "range": "± 31370",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 19165101,
            "range": "± 33669",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 158754310,
            "range": "± 728935",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 950837452,
            "range": "± 4288462",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 7411885,
            "range": "± 17915",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 9133003,
            "range": "± 32306",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 32405342,
            "range": "± 883891",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 243037274,
            "range": "± 6022661",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 8030210,
            "range": "± 8108",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 355024,
            "range": "± 660",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 677639922,
            "range": "± 1824932",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 96980,
            "range": "± 349",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 190333,
            "range": "± 3691",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 246232,
            "range": "± 4374",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 70426,
            "range": "± 256",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 70488,
            "range": "± 405",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 142186,
            "range": "± 117",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 165796,
            "range": "± 103",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 213130,
            "range": "± 113",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 80032,
            "range": "± 60",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 79926,
            "range": "± 55",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 160221,
            "range": "± 104",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 160136,
            "range": "± 134",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 200335,
            "range": "± 144",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 173898,
            "range": "± 76",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 173634,
            "range": "± 70",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 261233,
            "range": "± 151",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 261273,
            "range": "± 125",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 261154,
            "range": "± 490",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 3938483,
            "range": "± 1624",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 5963594,
            "range": "± 3521",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 25913056,
            "range": "± 9080",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 120738413,
            "range": "± 2132706",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1412186081,
            "range": "± 4977008",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 12033564354,
            "range": "± 39394551",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 3826198,
            "range": "± 2045",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 5853108,
            "range": "± 3503",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 25783332,
            "range": "± 132173",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 119445055,
            "range": "± 2235359",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1414949420,
            "range": "± 4958992",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 11993714830,
            "range": "± 59033626",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 3822589,
            "range": "± 3759",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 6648869,
            "range": "± 2835",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 24875796,
            "range": "± 133366",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 117942561,
            "range": "± 1397444",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1396000198,
            "range": "± 21991460",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 11870512627,
            "range": "± 10478964",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 3824432,
            "range": "± 5612",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 5367965,
            "range": "± 3814",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 29060910,
            "range": "± 139842",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 167116428,
            "range": "± 1404023",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1387709166,
            "range": "± 4613896",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 11896760730,
            "range": "± 26341037",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 3834911,
            "range": "± 2412",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 5502921,
            "range": "± 3078",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 79109666,
            "range": "± 639147",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 120028448,
            "range": "± 2329957",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1334531210,
            "range": "± 8674426",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 11848985098,
            "range": "± 23463102",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 4021595,
            "range": "± 26874",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 5604681,
            "range": "± 19859",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 23284044,
            "range": "± 108969",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 118611310,
            "range": "± 2559504",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1768704467,
            "range": "± 7715732",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 11399733611,
            "range": "± 34869362",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 5944147,
            "range": "± 532851",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 7612731,
            "range": "± 637131",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 26469244,
            "range": "± 746566",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 119202130,
            "range": "± 1364835",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 1035898291,
            "range": "± 2130904",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 13784861795,
            "range": "± 40016359",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 3826298,
            "range": "± 2619",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 38640338,
            "range": "± 739616",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 401551316,
            "range": "± 86811",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 4016734041,
            "range": "± 777051",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 40169020080,
            "range": "± 8589892",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 3822802,
            "range": "± 2629",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 38621384,
            "range": "± 739365",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 401417860,
            "range": "± 92272",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 4016261635,
            "range": "± 887030",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 40156462195,
            "range": "± 9054111",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 3824578,
            "range": "± 6811",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 38641556,
            "range": "± 743264",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 401683096,
            "range": "± 73141",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 4015835501,
            "range": "± 385572",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 40169477192,
            "range": "± 3752522",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 3829633,
            "range": "± 3371",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 38698003,
            "range": "± 736230",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 402396988,
            "range": "± 78104",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 4021924863,
            "range": "± 310582",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 40238539409,
            "range": "± 3408124",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 3983960,
            "range": "± 12497",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 40050062,
            "range": "± 716862",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 415422715,
            "range": "± 78351",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 4150191336,
            "range": "± 590481",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 41522724025,
            "range": "± 8749388",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 5243965,
            "range": "± 182677",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 48570475,
            "range": "± 1070945",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 497365734,
            "range": "± 1263674",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 4970643428,
            "range": "± 6293938",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 49846666568,
            "range": "± 84835948",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3801074,
            "range": "± 1680",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3800263,
            "range": "± 1962",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 3800298,
            "range": "± 2581",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 3800901,
            "range": "± 2564",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 3800349,
            "range": "± 1909",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 3822852,
            "range": "± 3288",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 5410416,
            "range": "± 4014",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 5411644,
            "range": "± 2785",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 5406459,
            "range": "± 3666",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 5412542,
            "range": "± 2767",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 3842453,
            "range": "± 2147",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 5673347,
            "range": "± 7775",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 23432305,
            "range": "± 25200",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 23441508,
            "range": "± 26172",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 23424285,
            "range": "± 21431",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 3859507,
            "range": "± 1959",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 5689334,
            "range": "± 2385",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 23447783,
            "range": "± 25645",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 120728045,
            "range": "± 2108469",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 121249812,
            "range": "± 2158402",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 3922259,
            "range": "± 4823",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 5644056,
            "range": "± 6358",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 26164726,
            "range": "± 38011",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 132934264,
            "range": "± 2041996",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8582",
            "value": 1004055728,
            "range": "± 3638227",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 4035569,
            "range": "± 37302",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 6750494,
            "range": "± 34827",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 44091932,
            "range": "± 54431",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 239897823,
            "range": "± 1560890",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 2293756744,
            "range": "± 5980893",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 3981216,
            "range": "± 2569",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 3798724,
            "range": "± 2229",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3980347,
            "range": "± 4874",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3797195,
            "range": "± 3107",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3977929,
            "range": "± 2316",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 3799170,
            "range": "± 2042",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 3977024,
            "range": "± 1679",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3795858,
            "range": "± 3207",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3980238,
            "range": "± 2126",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 3801836,
            "range": "± 1680",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 3974156,
            "range": "± 2894",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 3797384,
            "range": "± 1466",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 3979989,
            "range": "± 2734",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 3800001,
            "range": "± 1001",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3982242,
            "range": "± 3150",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 3800540,
            "range": "± 3146",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 3983653,
            "range": "± 1936",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 3802527,
            "range": "± 2051",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 3984197,
            "range": "± 3334",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 3806537,
            "range": "± 1756",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 3991505,
            "range": "± 4369",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 3802977,
            "range": "± 3179",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 4003838,
            "range": "± 2628",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 3805530,
            "range": "± 3511",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 4047607,
            "range": "± 4396",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3810333,
            "range": "± 1950",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 4140993,
            "range": "± 5447",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3805580,
            "range": "± 2338",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 4291007,
            "range": "± 9096",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 3809993,
            "range": "± 5809",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4563436,
            "range": "± 58244",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 3813556,
            "range": "± 18804",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 185830,
            "range": "± 4185",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 198927,
            "range": "± 1724",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 1062,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 751,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 468,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 87306,
            "range": "± 115",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1772000,
            "range": "± 21348",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 476062,
            "range": "± 3071",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 4164,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 2932,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1806,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 23,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 23,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 38,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 38,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 23,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 67,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 14,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 62,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 12678,
            "range": "± 51",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 78945,
            "range": "± 93",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 42,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 93,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 195,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 81,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 6137,
            "range": "± 8",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 129,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 4397,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 23258,
            "range": "± 105",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 20,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 11,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 265,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 37,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 167,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 12589,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 124677,
            "range": "± 7291",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 36,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 34,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6357,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 33683,
            "range": "± 56",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 20,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 37,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 581665,
            "range": "± 538",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 1156680,
            "range": "± 4072",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 1990433,
            "range": "± 1773",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_bytes_le",
            "value": 32037,
            "range": "± 16",
            "unit": "ns/iter"
          },
          {
            "name": "Block::serialize (bincode)",
            "value": 67766,
            "range": "± 38",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_string (serde_json)",
            "value": 221271,
            "range": "± 289",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_bytes_le",
            "value": 22626276,
            "range": "± 19191",
            "unit": "ns/iter"
          },
          {
            "name": "Block::deserialize (bincode)",
            "value": 22560510,
            "range": "± 26017",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_str (serde_json)",
            "value": 23600931,
            "range": "± 278326",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_bytes_le",
            "value": 345,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::serialize (bincode)",
            "value": 716,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_string (serde_json)",
            "value": 2420,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_bytes_le",
            "value": 227,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::deserialize (bincode)",
            "value": 348,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_str (serde_json)",
            "value": 14779,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_bytes_le",
            "value": 31827,
            "range": "± 29",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::serialize (bincode)",
            "value": 63915,
            "range": "± 19",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_string (serde_json)",
            "value": 208462,
            "range": "± 274",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_bytes_le",
            "value": 19382343,
            "range": "± 166742",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::deserialize (bincode)",
            "value": 19412461,
            "range": "± 16361",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_str (serde_json)",
            "value": 20020754,
            "range": "± 25673",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_bytes_le",
            "value": 8163,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::serialize (bincode)",
            "value": 16397,
            "range": "± 16",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_string (serde_json)",
            "value": 47100,
            "range": "± 67",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_bytes_le",
            "value": 4887322,
            "range": "± 6035",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::deserialize (bincode)",
            "value": 4867607,
            "range": "± 2885",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_str (serde_json)",
            "value": 5043147,
            "range": "± 9707",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_bytes_le",
            "value": 7587,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::serialize (bincode)",
            "value": 15649,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_string (serde_json)",
            "value": 43838,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_bytes_le",
            "value": 4055870,
            "range": "± 2220",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::deserialize (bincode)",
            "value": 4051619,
            "range": "± 8973",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_str (serde_json)",
            "value": 4197856,
            "range": "± 2969",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - deploy",
            "value": 64905115712,
            "range": "± 393665595",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - deployment",
            "value": 433639693,
            "range": "± 3369261",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - execution (transfer)",
            "value": 43430470969,
            "range": "± 103828888",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - execution (transfer)",
            "value": 55220206,
            "range": "± 142613",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 8336589620,
            "range": "± 17799597",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 313903311,
            "range": "± 670311",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 278785169,
            "range": "± 367012",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1395043948,
            "range": "± 8180125",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "committer": {
            "email": "9260812+howardwu@users.noreply.github.com",
            "name": "Howard Wu",
            "username": "howardwu"
          },
          "distinct": true,
          "id": "1c40a93728fa464cf8a98e657a2673ff56ca358a",
          "message": "Fix typo in comment",
          "timestamp": "2023-06-01T10:07:38-07:00",
          "tree_id": "87b07b3d1e3e66ed33570454a9598e1a6e0be75c",
          "url": "https://github.com/AleoHQ/snarkVM/commit/1c40a93728fa464cf8a98e657a2673ff56ca358a"
        },
        "date": 1685655229453,
        "tool": "cargo",
        "benches": [
          {
            "name": "VariableBase MSM on BLS12-377 (10000)",
            "value": 109986690,
            "range": "± 418531",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (100000)",
            "value": 767153601,
            "range": "± 2275085",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (200000)",
            "value": 1404582607,
            "range": "± 3671374",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (300000)",
            "value": 2163905394,
            "range": "± 17717869",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (400000)",
            "value": 2736031910,
            "range": "± 9927101",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (500000)",
            "value": 3063225073,
            "range": "± 12293163",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (1000000)",
            "value": 5626848168,
            "range": "± 17701263",
            "unit": "ns/iter"
          },
          {
            "name": "VariableBase MSM on BLS12-377 (2000000)",
            "value": 10067156439,
            "range": "± 14041203",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (10000)",
            "value": 71633929,
            "range": "± 146530",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (100000)",
            "value": 530925388,
            "range": "± 8862655",
            "unit": "ns/iter"
          },
          {
            "name": "Variable MSM on Edwards-BLS12 (1000000)",
            "value": 5158126239,
            "range": "± 128427119",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 4",
            "value": 96523,
            "range": "± 340",
            "unit": "ns/iter"
          },
          {
            "name": "PoseidonSponge<2, 1> Absorb 10",
            "value": 241042,
            "range": "± 840",
            "unit": "ns/iter"
          },
          {
            "name": "snark_universal_setup",
            "value": 1734734717,
            "range": "± 12639677",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_100",
            "value": 103221807,
            "range": "± 929264",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_1000",
            "value": 635750347,
            "range": "± 2913816",
            "unit": "ns/iter"
          },
          {
            "name": "snark_circuit_setup_10000",
            "value": 10483747386,
            "range": "± 17306466",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/compressed",
            "value": 8159,
            "range": "± 12",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_serialize/uncompressed",
            "value": 8499,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_checked",
            "value": 30857706,
            "range": "± 1010279",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/compressed_unchecked",
            "value": 14306028,
            "range": "± 23230",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_checked",
            "value": 22798926,
            "range": "± 679584",
            "unit": "ns/iter"
          },
          {
            "name": "snark_vk_deserialize/uncompressed_unchecked",
            "value": 6088393,
            "range": "± 14690",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100",
            "value": 7585578,
            "range": "± 66633",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_1000",
            "value": 20169085,
            "range": "± 1140397",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_10000",
            "value": 166626583,
            "range": "± 775798",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_prove_100000",
            "value": 1017740719,
            "range": "± 2165007",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100",
            "value": 7897163,
            "range": "± 74681",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_1000",
            "value": 9821315,
            "range": "± 187537",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_10000",
            "value": 35794726,
            "range": "± 976077",
            "unit": "ns/iter"
          },
          {
            "name": "snark_certificate_verify_100000",
            "value": 283212259,
            "range": "± 1863254",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add",
            "value": 8294353,
            "range": "± 30236",
            "unit": "ns/iter"
          },
          {
            "name": "LinearCombination::add_assign",
            "value": 402644,
            "range": "± 745",
            "unit": "ns/iter"
          },
          {
            "name": "debug",
            "value": 873099574,
            "range": "± 2245324",
            "unit": "ns/iter"
          },
          {
            "name": "account_private_key",
            "value": 107230,
            "range": "± 123",
            "unit": "ns/iter"
          },
          {
            "name": "account_view_key",
            "value": 207422,
            "range": "± 4191",
            "unit": "ns/iter"
          },
          {
            "name": "account_address",
            "value": 274196,
            "range": "± 5707",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 1",
            "value": 76898,
            "range": "± 71",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 4 -> 2",
            "value": 76637,
            "range": "± 154",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 1",
            "value": 153703,
            "range": "± 401",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 4",
            "value": 179852,
            "range": "± 189",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon2 Hash 10 -> 8",
            "value": 230896,
            "range": "± 793",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 1",
            "value": 90454,
            "range": "± 219",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 4 -> 2",
            "value": 90632,
            "range": "± 102",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 1",
            "value": 180671,
            "range": "± 198",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 4",
            "value": 180263,
            "range": "± 318",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon4 Hash 10 -> 8",
            "value": 225676,
            "range": "± 606",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 1",
            "value": 202269,
            "range": "± 252",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 4 -> 2",
            "value": 202304,
            "range": "± 109",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 1",
            "value": 305168,
            "range": "± 532",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 4",
            "value": 305146,
            "range": "± 660",
            "unit": "ns/iter"
          },
          {
            "name": "Poseidon8 Hash 10 -> 8",
            "value": 305207,
            "range": "± 276",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1",
            "value": 4130087,
            "range": "± 4624",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10",
            "value": 6236659,
            "range": "± 2540",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100",
            "value": 26919710,
            "range": "± 23690",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/1000",
            "value": 124184952,
            "range": "± 2230793",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/10000",
            "value": 1462906674,
            "range": "± 6752658",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/new/100000",
            "value": 12459121335,
            "range": "± 29019950",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1",
            "value": 4720685,
            "range": "± 2718",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10",
            "value": 7069525,
            "range": "± 4072",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100",
            "value": 30148259,
            "range": "± 1410912",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/1000",
            "value": 122545004,
            "range": "± 2394417",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/10000",
            "value": 1459197344,
            "range": "± 6415466",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1/100000",
            "value": 12429786510,
            "range": "± 29744190",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1",
            "value": 4714602,
            "range": "± 3292",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10",
            "value": 8046263,
            "range": "± 3747",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100",
            "value": 29030739,
            "range": "± 1332495",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/1000",
            "value": 122404789,
            "range": "± 1680845",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/10000",
            "value": 1457423960,
            "range": "± 6869891",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10/100000",
            "value": 12432767505,
            "range": "± 22005621",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1",
            "value": 4720593,
            "range": "± 3889",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10",
            "value": 6490873,
            "range": "± 7653",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100",
            "value": 34275679,
            "range": "± 1696539",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/1000",
            "value": 179503737,
            "range": "± 2901343",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/10000",
            "value": 1453479033,
            "range": "± 7429832",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100/100000",
            "value": 12427516043,
            "range": "± 39463508",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1",
            "value": 4729790,
            "range": "± 2729",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10",
            "value": 6640195,
            "range": "± 7341",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100",
            "value": 84875570,
            "range": "± 1662362",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/1000",
            "value": 124944625,
            "range": "± 2505758",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/10000",
            "value": 1396858192,
            "range": "± 20797337",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/1000/100000",
            "value": 12384438404,
            "range": "± 21249031",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1",
            "value": 4961714,
            "range": "± 25363",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10",
            "value": 6756399,
            "range": "± 7831",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100",
            "value": 27082515,
            "range": "± 1221929",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/1000",
            "value": 123540507,
            "range": "± 1088667",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/10000",
            "value": 1843871188,
            "range": "± 9103213",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/10000/100000",
            "value": 11820460017,
            "range": "± 17940422",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1",
            "value": 7455805,
            "range": "± 822517",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10",
            "value": 9382010,
            "range": "± 800827",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100",
            "value": 31131368,
            "range": "± 872460",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/1000",
            "value": 134007550,
            "range": "± 3918964",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/10000",
            "value": 1076011376,
            "range": "± 7164135",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/append/100000/100000",
            "value": 14360024689,
            "range": "± 21374102",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1",
            "value": 4011321,
            "range": "± 2430",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10",
            "value": 40102635,
            "range": "± 32845",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/100",
            "value": 401114732,
            "range": "± 157244",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/1000",
            "value": 4006916786,
            "range": "± 848823",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1/10000",
            "value": 40096929795,
            "range": "± 6131677",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1",
            "value": 4008295,
            "range": "± 2384",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10",
            "value": 40110880,
            "range": "± 19324",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/100",
            "value": 401062301,
            "range": "± 232385",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/1000",
            "value": 4008001028,
            "range": "± 1259694",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10/10000",
            "value": 40077349692,
            "range": "± 5366587",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1",
            "value": 4009817,
            "range": "± 2968",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10",
            "value": 40109524,
            "range": "± 20342",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/100",
            "value": 401182589,
            "range": "± 356512",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/1000",
            "value": 4010231460,
            "range": "± 1343718",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100/10000",
            "value": 40113971816,
            "range": "± 6668277",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1",
            "value": 4015882,
            "range": "± 5212",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10",
            "value": 40139703,
            "range": "± 46723",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/100",
            "value": 401635058,
            "range": "± 189116",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/1000",
            "value": 4016520915,
            "range": "± 770983",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/1000/10000",
            "value": 40160665588,
            "range": "± 10194761",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1",
            "value": 4202822,
            "range": "± 11386",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10",
            "value": 41836421,
            "range": "± 60186",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/100",
            "value": 416545701,
            "range": "± 419941",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/1000",
            "value": 4165905328,
            "range": "± 3107215",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/10000/10000",
            "value": 41678610121,
            "range": "± 18161526",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1",
            "value": 5878056,
            "range": "± 107522",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10",
            "value": 53664817,
            "range": "± 904309",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/100",
            "value": 531995781,
            "range": "± 6987602",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/1000",
            "value": 5295713597,
            "range": "± 28381868",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update/100000/10000",
            "value": 52751756966,
            "range": "± 208846754",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1",
            "value": 3987827,
            "range": "± 5614",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #2",
            "value": 3986020,
            "range": "± 2101",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #3",
            "value": 3986225,
            "range": "± 3902",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #4",
            "value": 3987088,
            "range": "± 2553",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1/1 #5",
            "value": 3989206,
            "range": "± 2312",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/1",
            "value": 3988651,
            "range": "± 5629",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10",
            "value": 5605839,
            "range": "± 5553",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #2",
            "value": 5606467,
            "range": "± 2907",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #3",
            "value": 5602880,
            "range": "± 38573",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10/10 #4",
            "value": 5605312,
            "range": "± 6528",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/1",
            "value": 3983398,
            "range": "± 2986",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/10",
            "value": 5847779,
            "range": "± 3045",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100",
            "value": 23785796,
            "range": "± 37263",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #2",
            "value": 23795723,
            "range": "± 43095",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100/100 #3",
            "value": 23799346,
            "range": "± 43759",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1",
            "value": 3987034,
            "range": "± 4675",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/10",
            "value": 5847324,
            "range": "± 2906",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/100",
            "value": 23769930,
            "range": "± 18383",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000",
            "value": 126202804,
            "range": "± 1593290",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/1000/1000 #2",
            "value": 124817470,
            "range": "± 1777928",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1",
            "value": 4025340,
            "range": "± 5734",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/10",
            "value": 5764443,
            "range": "± 11494",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/100",
            "value": 26704043,
            "range": "± 71863",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/1000",
            "value": 138115109,
            "range": "± 2149240",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/10000/8669",
            "value": 1040744449,
            "range": "± 6159077",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1",
            "value": 4065268,
            "range": "± 10347",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10",
            "value": 7662470,
            "range": "± 46016",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/100",
            "value": 44494040,
            "range": "± 130841",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/1000",
            "value": 253598610,
            "range": "± 2479458",
            "unit": "ns/iter"
          },
          {
            "name": "MerkleTree/update_many/100000/10000",
            "value": 2355812068,
            "range": "± 10036420",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/1",
            "value": 3990121,
            "range": "± 2684",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/1",
            "value": 3989296,
            "range": "± 1783",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/2",
            "value": 3986016,
            "range": "± 4116",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/2",
            "value": 3988982,
            "range": "± 3762",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/3",
            "value": 3984808,
            "range": "± 2492",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/3",
            "value": 3986530,
            "range": "± 2508",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/4",
            "value": 3986137,
            "range": "± 2456",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/4",
            "value": 3987614,
            "range": "± 3806",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/5",
            "value": 3986825,
            "range": "± 2669",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/5",
            "value": 3988687,
            "range": "± 2709",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/6",
            "value": 3983760,
            "range": "± 3360",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/6",
            "value": 3983099,
            "range": "± 3132",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/7",
            "value": 3983976,
            "range": "± 4388",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/7",
            "value": 3984268,
            "range": "± 2720",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/8",
            "value": 3982938,
            "range": "± 4370",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/8",
            "value": 3989224,
            "range": "± 6024",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/9",
            "value": 3989845,
            "range": "± 1920",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/9",
            "value": 3988200,
            "range": "± 2228",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/10",
            "value": 3993717,
            "range": "± 4709",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/10",
            "value": 3990912,
            "range": "± 3190",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/11",
            "value": 4005356,
            "range": "± 2371",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/11",
            "value": 3991316,
            "range": "± 3838",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/12",
            "value": 4017583,
            "range": "± 4636",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/12",
            "value": 3984591,
            "range": "± 9007",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/13",
            "value": 4059248,
            "range": "± 4429",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/13",
            "value": 3984672,
            "range": "± 4446",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/14",
            "value": 4168482,
            "range": "± 7602",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/14",
            "value": 3993176,
            "range": "± 4867",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/15",
            "value": 4369132,
            "range": "± 31198",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/15",
            "value": 3998765,
            "range": "± 11896",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Single/16",
            "value": 4817232,
            "range": "± 34928",
            "unit": "ns/iter"
          },
          {
            "name": "UpdateVSUpdateMany/Batch/16",
            "value": 4008251,
            "range": "± 17359",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_rand",
            "value": 189872,
            "range": "± 3621",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_mul_assign",
            "value": 208051,
            "range": "± 2996",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign",
            "value": 1132,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_add_assign_mixed",
            "value": 823,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_double",
            "value": 528,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g1_is_in_correct_subgroup",
            "value": 89656,
            "range": "± 266",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_rand",
            "value": 1820289,
            "range": "± 10197",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_mul_assign",
            "value": 498112,
            "range": "± 2117",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign",
            "value": 4322,
            "range": "± 24",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_add_assign_mixed",
            "value": 3068,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: g2_double",
            "value": 1937,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_add_nocarry",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_sub_noborrow",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_mul2",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_repr_div2",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_add_assign",
            "value": 18,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sub_assign",
            "value": 7,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_mul_assign",
            "value": 71,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_double",
            "value": 13,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_square",
            "value": 64,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_inverse",
            "value": 13032,
            "range": "± 75",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_negate",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_sqrt",
            "value": 80004,
            "range": "± 202",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_to_bigint",
            "value": 42,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq_from_bigint",
            "value": 80,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_add_assign",
            "value": 246,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_sub_assign",
            "value": 146,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_mul_assign",
            "value": 6453,
            "range": "± 17",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_double",
            "value": 167,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_square",
            "value": 4442,
            "range": "± 34",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq12_inverse",
            "value": 24877,
            "range": "± 70",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_add_assign",
            "value": 25,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sub_assign",
            "value": 12,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_mul_assign",
            "value": 259,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_double",
            "value": 21,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_square",
            "value": 208,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_inverse",
            "value": 14089,
            "range": "± 38",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fq2_sqrt",
            "value": 126417,
            "range": "± 5326",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_add_nocarry",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_sub_noborrow",
            "value": 6,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_num_bits",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_mul2",
            "value": 10,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_repr_div2",
            "value": 9,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_add_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sub_assign",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_mul_assign",
            "value": 37,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_double",
            "value": 5,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_square",
            "value": 36,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_inverse",
            "value": 6817,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_negate",
            "value": 4,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_sqrt",
            "value": 34210,
            "range": "± 71",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_to_bigint",
            "value": 24,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: fr_from_bigint",
            "value": 38,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_miller_loop",
            "value": 592720,
            "range": "± 1189",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_final_exponentiation",
            "value": 1192766,
            "range": "± 3391",
            "unit": "ns/iter"
          },
          {
            "name": "bls12_377: pairing_full",
            "value": 2053891,
            "range": "± 5470",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_bytes_le",
            "value": 34285,
            "range": "± 48",
            "unit": "ns/iter"
          },
          {
            "name": "Block::serialize (bincode)",
            "value": 71273,
            "range": "± 96",
            "unit": "ns/iter"
          },
          {
            "name": "Block::to_string (serde_json)",
            "value": 254545,
            "range": "± 296",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_bytes_le",
            "value": 23416910,
            "range": "± 69031",
            "unit": "ns/iter"
          },
          {
            "name": "Block::deserialize (bincode)",
            "value": 23516741,
            "range": "± 135925",
            "unit": "ns/iter"
          },
          {
            "name": "Block::from_str (serde_json)",
            "value": 24239537,
            "range": "± 47057",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_bytes_le",
            "value": 448,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::serialize (bincode)",
            "value": 925,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "Header::to_string (serde_json)",
            "value": 3119,
            "range": "± 26",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_bytes_le",
            "value": 234,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::deserialize (bincode)",
            "value": 384,
            "range": "± 0",
            "unit": "ns/iter"
          },
          {
            "name": "Header::from_str (serde_json)",
            "value": 17208,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_bytes_le",
            "value": 33521,
            "range": "± 75",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::serialize (bincode)",
            "value": 67580,
            "range": "± 73",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::to_string (serde_json)",
            "value": 244498,
            "range": "± 245",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_bytes_le",
            "value": 20133493,
            "range": "± 56568",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::deserialize (bincode)",
            "value": 20237119,
            "range": "± 91498",
            "unit": "ns/iter"
          },
          {
            "name": "Transactions::from_str (serde_json)",
            "value": 20879256,
            "range": "± 36381",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_bytes_le",
            "value": 8658,
            "range": "± 28",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::serialize (bincode)",
            "value": 17171,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::to_string (serde_json)",
            "value": 57458,
            "range": "± 99",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_bytes_le",
            "value": 5085506,
            "range": "± 8986",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::deserialize (bincode)",
            "value": 5084643,
            "range": "± 28057",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction::from_str (serde_json)",
            "value": 5297322,
            "range": "± 13966",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_bytes_le",
            "value": 8165,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::serialize (bincode)",
            "value": 16736,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::to_string (serde_json)",
            "value": 53336,
            "range": "± 90",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_bytes_le",
            "value": 4260032,
            "range": "± 11160",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::deserialize (bincode)",
            "value": 4234743,
            "range": "± 25991",
            "unit": "ns/iter"
          },
          {
            "name": "Transition::from_str (serde_json)",
            "value": 4414433,
            "range": "± 12214",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - deploy",
            "value": 70437815866,
            "range": "± 135447327",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - deployment",
            "value": 504374822,
            "range": "± 8140487",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction - execution (transfer)",
            "value": 48007680543,
            "range": "± 180994779",
            "unit": "ns/iter"
          },
          {
            "name": "Transaction verify - execution (transfer)",
            "value": 59279997,
            "range": "± 1144237",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Trim 2^13",
            "value": 8574371076,
            "range": "± 11570819",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Prove 2^13",
            "value": 333278310,
            "range": "± 1591310",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 10 of 2^13",
            "value": 290015224,
            "range": "± 1002231",
            "unit": "ns/iter"
          },
          {
            "name": "CoinbasePuzzle::Accumulate 100 of 2^13",
            "value": 1426009619,
            "range": "± 8746748",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}