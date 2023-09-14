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

use super::*;
use snarkvm_utilities::{bits_from_bytes_le, bytes_from_bits_le};

impl<const TYPE: u8, const VARIANT: usize> Hash for Keccak<TYPE, VARIANT> {
    type Input = bool;
    type Output = Vec<bool>;

    /// Returns the Keccak hash of the given input as bits.
    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Result<Self::Output> {
        let result = match (TYPE, VARIANT) {
            (0, 224) => bits_from_bytes_le(&keccak_224_native(&bytes_from_bits_le(input))).collect(),
            (0, 256) => bits_from_bytes_le(&keccak_256_native(&bytes_from_bits_le(input))).collect(),
            (0, 384) => bits_from_bytes_le(&keccak_384_native(&bytes_from_bits_le(input))).collect(),
            (0, 512) => bits_from_bytes_le(&keccak_512_native(&bytes_from_bits_le(input))).collect(),
            (1, 224) => bits_from_bytes_le(&sha3_224_native(&bytes_from_bits_le(input))).collect(),
            (1, 256) => bits_from_bytes_le(&sha3_256_native(&bytes_from_bits_le(input))).collect(),
            (1, 384) => bits_from_bytes_le(&sha3_384_native(&bytes_from_bits_le(input))).collect(),
            (1, 512) => bits_from_bytes_le(&sha3_512_native(&bytes_from_bits_le(input))).collect(),
            _ => unreachable!("Invalid Keccak type and variant"),
        };
        Ok(result)
    }
}

/// Computes the Keccak-224 hash of the given preimage as bytes.
fn keccak_224_native(preimage: &[u8]) -> [u8; 28] {
    let mut keccak = TinyKeccak::v224();
    keccak.update(preimage);

    let mut hash = [0u8; 28];
    keccak.finalize(&mut hash);
    hash
}

/// Computes the Keccak-256 hash of the given preimage as bytes.
fn keccak_256_native(preimage: &[u8]) -> [u8; 32] {
    let mut keccak = TinyKeccak::v256();
    keccak.update(preimage);

    let mut hash = [0u8; 32];
    keccak.finalize(&mut hash);
    hash
}

/// Computes the Keccak-384 hash of the given preimage as bytes.
fn keccak_384_native(preimage: &[u8]) -> [u8; 48] {
    let mut keccak = TinyKeccak::v384();
    keccak.update(preimage);

    let mut hash = [0u8; 48];
    keccak.finalize(&mut hash);
    hash
}

/// Computes the Keccak-512 hash of the given preimage as bytes.
fn keccak_512_native(preimage: &[u8]) -> [u8; 64] {
    let mut keccak = TinyKeccak::v512();
    keccak.update(preimage);

    let mut hash = [0u8; 64];
    keccak.finalize(&mut hash);
    hash
}

/// Computes the SHA3-224 hash of the given preimage as bytes.
fn sha3_224_native(preimage: &[u8]) -> [u8; 28] {
    let mut keccak = TinySha3::v224();
    keccak.update(preimage);

    let mut hash = [0u8; 28];
    keccak.finalize(&mut hash);
    hash
}

/// Computes the SHA3-256 hash of the given preimage as bytes.
fn sha3_256_native(preimage: &[u8]) -> [u8; 32] {
    let mut keccak = TinySha3::v256();
    keccak.update(preimage);

    let mut hash = [0u8; 32];
    keccak.finalize(&mut hash);
    hash
}

/// Computes the SHA3-384 hash of the given preimage as bytes.
fn sha3_384_native(preimage: &[u8]) -> [u8; 48] {
    let mut keccak = TinySha3::v384();
    keccak.update(preimage);

    let mut hash = [0u8; 48];
    keccak.finalize(&mut hash);
    hash
}

/// Computes the SHA3-512 hash of the given preimage as bytes.
fn sha3_512_native(preimage: &[u8]) -> [u8; 64] {
    let mut keccak = TinySha3::v512();
    keccak.update(preimage);

    let mut hash = [0u8; 64];
    keccak.finalize(&mut hash);
    hash
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Rng;
    use snarkvm_utilities::{bits_from_bytes_le, bytes_from_bits_le};

    macro_rules! check_equivalence {
        ($console:expr, $native:expr) => {
            let rng = &mut TestRng::default();

            let mut input_sizes = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 32, 64, 128, 256, 512, 1024];
            input_sizes.extend((0..100).map(|_| rng.gen_range(1..1024)));

            for num_inputs in input_sizes {
                println!("Checking equivalence for {num_inputs} inputs");

                // Prepare the preimage.
                let input = (0..num_inputs).map(|_| Uniform::rand(rng)).collect::<Vec<bool>>();

                // Compute the native hash.
                let expected = $native(&bytes_from_bits_le(&input));
                let expected = bits_from_bytes_le(&expected).collect::<Vec<_>>();

                // Compute the console hash.
                let candidate = $console.hash(&input).unwrap();
                assert_eq!(expected, candidate);
            }
        };
    }

    #[test]
    fn test_keccak_224_equivalence() {
        check_equivalence!(Keccak224::default(), keccak_224_native);
    }

    #[test]
    fn test_keccak_256_equivalence() {
        check_equivalence!(Keccak256::default(), keccak_256_native);
    }

    #[test]
    fn test_keccak_384_equivalence() {
        check_equivalence!(Keccak384::default(), keccak_384_native);
    }

    #[test]
    fn test_keccak_512_equivalence() {
        check_equivalence!(Keccak512::default(), keccak_512_native);
    }

    // Show that you can call keccak on an empty string of bits.
    #[test]
    fn test_keccak_256_on_constants_empty() {
        let input = vec![];
        // This is the tiny-keccak (native) result, which is the same as the console version:
        // let result = keccak_256_native(&bytes_from_bits_le(&input));
        let resultbits = Keccak256::default().hash(&input).unwrap();
        let result = bytes_from_bits_le(&resultbits);
        println!("{:?}", result);  // This result has been checked against ACL2.
    }

    // Show collisions from different bit lengths.  This is why it is misleading to call the function keccak.
    // Standard keccak gives different results on different bit lengths.
    // The function should really be called something like byteify_then_keccak.
    // For 
    // In the case of sha3, not supporting other bit lengths might be too limiting.
    #[test]
    fn test_keccak_256_on_constants_0_00() {
        let input0 = vec![false];
        let input00 = vec![false, false];
        // let result0 = keccak_256_native(&bytes_from_bits_le(&input0));
        // let result00 = keccak_256_native(&bytes_from_bits_le(&input00));
        let result0bits = Keccak256::default().hash(&input0).unwrap();
        let result00bits = Keccak256::default().hash(&input00).unwrap();
        let result0 = bytes_from_bits_le(&result0bits);
        let result00 = bytes_from_bits_le(&result00bits);
        assert_eq!(result0, result00);
    }

    // Show another collision.
    #[test]
    fn test_keccak_256_on_constants_1_10() {
        let input1 = vec![true];
        let input10 = vec![true, false];
        // let result1 = keccak_256_native(&bytes_from_bits_le(&input1));
        // let result10 = keccak_256_native(&bytes_from_bits_le(&input10));
        let result1bits = Keccak256::default().hash(&input1).unwrap();
        let result10bits = Keccak256::default().hash(&input10).unwrap();
        let result1 = bytes_from_bits_le(&result1bits);
        let result10 = bytes_from_bits_le(&result10bits);
        // println!("{:?}", result1);
        // println!("{:?}", result10);
        assert_eq!(result1, result10);
    }

    #[test]
    fn test_sha3_224_equivalence() {
        check_equivalence!(Sha3_224::default(), sha3_224_native);
    }

    #[test]
    fn test_sha3_256_equivalence() {
        check_equivalence!(Sha3_256::default(), sha3_256_native);
    }

    #[test]
    fn test_sha3_384_equivalence() {
        check_equivalence!(Sha3_384::default(), sha3_384_native);
    }

    #[test]
    fn test_sha3_512_equivalence() {
        check_equivalence!(Sha3_512::default(), sha3_512_native);
    }
}
