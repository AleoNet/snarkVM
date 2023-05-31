window.BENCHMARK_DATA = {
  "lastUpdate": 1685493786018,
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
      }
    ]
  }
}