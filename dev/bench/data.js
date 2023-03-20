window.BENCHMARK_DATA = {
  "lastUpdate": 1679340894138,
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
      }
    ]
  }
}