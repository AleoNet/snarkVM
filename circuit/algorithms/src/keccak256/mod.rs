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

#[cfg(all(test, console))]
use snarkvm_circuit_types::environment::assert_scope;
#[cfg(test)]
use snarkvm_utilities::{TestRng, Uniform};

use crate::Hash;
use snarkvm_circuit_types::{environment::prelude::*, Boolean, U64};

/// The Keccak-224 hash function.
pub type Keccak224<E> = Keccak<E, { KeccakType::Keccak as u8 }, 224>;
/// The Keccak-256 hash function.
pub type Keccak256<E> = Keccak<E, { KeccakType::Keccak as u8 }, 256>;
/// The Keccak-384 hash function.
pub type Keccak384<E> = Keccak<E, { KeccakType::Keccak as u8 }, 384>;
/// The Keccak-512 hash function.
pub type Keccak512<E> = Keccak<E, { KeccakType::Keccak as u8 }, 512>;

/// The SHA3-224 hash function.
pub type Sha3_224<E> = Keccak<E, { KeccakType::Sha3 as u8 }, 224>;
/// The SHA3-256 hash function.
pub type Sha3_256<E> = Keccak<E, { KeccakType::Sha3 as u8 }, 256>;
/// The SHA3-384 hash function.
pub type Sha3_384<E> = Keccak<E, { KeccakType::Sha3 as u8 }, 384>;
/// The SHA3-512 hash function.
pub type Sha3_512<E> = Keccak<E, { KeccakType::Sha3 as u8 }, 512>;

/// A helper to specify the hash type.
enum KeccakType {
    Keccak,
    Sha3,
}

/// The rows and columns are 5-bit lanes.
const MODULO: usize = 5;
/// The permutation type `l`.
const L: usize = 6;
/// The number of rounds in a full-round operation.
const NUM_ROUNDS: usize = 12 + 2 * L;

/// The sponge construction `Sponge[f, pad, r]` is a function that takes a variable-length input
/// and produces a fixed-length output (the hash value).
///
/// The permutation `f` is a function that takes a fixed-length input and produces a fixed-length output,
/// defined as `f = Keccak-f[b]`, where `b := 25 * 2^l` is the width of the permutation,
/// and `l` is the log width of the permutation.
/// For our case, `l = 6`, thus `b = 1600`.
///
/// The padding rule `pad` is a function that takes a variable-length input and produces a fixed-length output.
/// In Keccak, `pad` is a multi-rate padding, defined as `pad(M) = M || 0x01 || 0x00…0x00 || 0x80`,
/// where `M` is the input data, and `0x01 || 0x00…0x00 || 0x80` is the padding.
/// In SHA-3, `pad` is a SHAKE, defined as `pad(M) = M || 0x06 || 0x00…0x00 || 0x80`,
/// where `M` is the input data, and `0x06 || 0x00…0x00 || 0x80` is the padding.
///
/// The bitrate `r` is the number of bits that are absorbed into the sponge state in each iteration
/// of the absorbing phase.
///
/// In addition, the capacity is defined as `c := b - r`.
pub struct Keccak<E: Environment, const TYPE: u8, const VARIANT: usize> {
    /// The round constants `RC[t] ∈ GF(2)` are defined as the
    /// output of a linear feedback shift register (LFSR).
    round_constants: Vec<U64<E>>,
    /// Precomputations for the ρ step.
    rotl: Vec<usize>,
}

impl<E: Environment, const TYPE: u8, const VARIANT: usize> Keccak<E, TYPE, VARIANT> {
    /// Initializes a new Keccak hash function.
    pub fn new() -> Self {
        Self {
            round_constants: Self::ROUND_CONSTANTS.into_iter().map(|e| U64::constant(console::U64::new(e))).collect(),
            rotl: Self::rotl_offsets::<NUM_ROUNDS>(),
        }
    }
}

impl<E: Environment, const TYPE: u8, const VARIANT: usize> Hash for Keccak<E, TYPE, VARIANT> {
    type Input = Boolean<E>;
    type Output = Vec<Boolean<E>>;

    /// Returns the Keccak hash of the given input as bits.
    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        /// The permutation width `b`.
        const PERMUTATION_WIDTH: usize = 1600;

        // The bitrate `r`.
        let bitrate = (200 - (VARIANT / 4)) * 8;
        debug_assert!(bitrate < PERMUTATION_WIDTH, "The bitrate must be less than the permutation width");

        // Ensure the input is not empty.
        if input.is_empty() {
            E::halt("The input to the hash function must not be empty")
        }

        // The root state `s` is defined as `0^b`.
        let mut s = vec![Boolean::constant(false); PERMUTATION_WIDTH];

        // The padded blocks `P`.
        let padded_blocks = match TYPE {
            0 => Self::pad_keccak(input, bitrate),
            1 => Self::pad_sha3(input, bitrate),
            2.. => unreachable!("Invalid Keccak type"),
        };

        /* The first part of the sponge construction (the absorbing phase):
         *
         * for i = 0 to |P|_r − 1 do
         *   s = s ⊕ (P_i || 0^c) # Note: |P_i| + c == b, since |P_i| == r
         *   s = f(s)
         * end for
         */
        for block in padded_blocks {
            // s = s ⊕ (P_i || 0^c)
            for (j, bit) in block.into_iter().enumerate() {
                s[j] = &s[j] ^ &bit;
            }
            // s = f(s)
            s = Self::permutation_f::<PERMUTATION_WIDTH, NUM_ROUNDS>(s, &self.round_constants, &self.rotl);
        }

        /* The second part of the sponge construction (the squeezing phase):
         *
         * Z = s[0..r-1]
         * while |Z|_r < l do
         *   s = f(s)
         *   Z = Z || s[0..r-1]
         * end while
         * return Z[0..l-1]
         */
        // Z = s[0..r-1]
        let mut z = s[..bitrate].to_vec();
        // while |Z|_r < l do
        while z.len() < VARIANT {
            // s = f(s)
            s = Self::permutation_f::<PERMUTATION_WIDTH, NUM_ROUNDS>(s, &self.round_constants, &self.rotl);
            // Z = Z || s[0..r-1]
            z.extend(s.iter().take(bitrate).cloned());
        }
        // return Z[0..l-1]
        z.into_iter().take(VARIANT).collect()
    }
}

impl<E: Environment, const TYPE: u8, const VARIANT: usize> Keccak<E, TYPE, VARIANT> {
    /// The values `ROUND_CONSTANTS[t] ∈ GF(2)` are defined as the
    /// output of a binary linear feedback shift register (LFSR):
    /// ```text
    /// ROUND_CONSTANTS[t] = (x^t) mod (x^8 + x^6 + x^5 + x^4 + 1) mod x in GF(2)[x]
    /// ```
    /// where `t ∈ {0, 1, …, NUM_ROUNDS}`.
    const ROUND_CONSTANTS: [u64; NUM_ROUNDS] = [
        0x0000000000000001,
        0x0000000000008082,
        0x800000000000808A,
        0x8000000080008000,
        0x000000000000808B,
        0x0000000080000001,
        0x8000000080008081,
        0x8000000000008009,
        0x000000000000008A,
        0x0000000000000088,
        0x0000000080008009,
        0x000000008000000A,
        0x000000008000808B,
        0x800000000000008B,
        0x8000000000008089,
        0x8000000000008003,
        0x8000000000008002,
        0x8000000000000080,
        0x000000000000800A,
        0x800000008000000A,
        0x8000000080008081,
        0x8000000000008080,
        0x0000000080000001,
        0x8000000080008008,
    ];

    /// Returns the ROTL offsets for the ρ step.
    ///
    /// The offsets are defined as follows:
    /// ```text
    /// for t = 0 to NUM_ROUNDS do
    ///   offset[t] = (t + 1)(t + 2)/2
    /// end for
    /// ```
    ///
    /// This method transposes the offsets to match the access pattern (i.e. for y, then for x).
    fn rotl_offsets<const NUM_ROUNDS: usize>() -> Vec<usize> {
        let mut rotl = vec![0; MODULO * MODULO];
        let mut x: usize = 1;
        let mut y: usize = 0;

        for t in 0..NUM_ROUNDS {
            let rotr = ((t + 1) * (t + 2) / 2) % 64;
            rotl[x + (y * MODULO)] = (64 - rotr) % 64;

            // Update x and y.
            let x_old = x;
            x = y;
            y = (2 * x_old + 3 * y) % MODULO;
        }
        rotl
    }

    /// In Keccak, `pad` is a multi-rate padding, defined as `pad(M) = M || 0x01 || 0x00…0x00 || 0x80`,
    /// where `M` is the input data, and `0x01 || 0x00…0x00 || 0x80` is the padding.
    /// The padding extends the input data to a multiple of the bitrate `r`, defined as `r = b - c`,
    /// where `b` is the width of the permutation, and `c` is the capacity.
    fn pad_keccak(input: &[Boolean<E>], bitrate: usize) -> Vec<Vec<Boolean<E>>> {
        debug_assert!(bitrate > 0, "The bitrate must be positive");

        // Resize the input to a multiple of 8.
        let mut padded_input = input.to_vec();
        padded_input.resize((input.len() + 7) / 8 * 8, Boolean::constant(false));

        // Step 1: Append the bit "1" to the message.
        padded_input.push(Boolean::constant(true));

        // Step 2: Append "0" bits until the length of the message is congruent to r-1 mod r.
        while (padded_input.len() % bitrate) != (bitrate - 1) {
            padded_input.push(Boolean::constant(false));
        }

        // Step 3: Append the bit "1" to the message.
        padded_input.push(Boolean::constant(true));

        // Construct the padded blocks.
        let mut result = Vec::new();
        for block in padded_input.chunks(bitrate) {
            result.push(block.to_vec());
        }
        result
    }

    /// In SHA-3, `pad` is a SHAKE, defined as `pad(M) = M || 0x06 || 0x00…0x00 || 0x80`,
    /// where `M` is the input data, and `0x06 || 0x00…0x00 || 0x80` is the padding.
    /// The padding extends the input data to a multiple of the bitrate `r`, defined as `r = b - c`,
    /// where `b` is the width of the permutation, and `c` is the capacity.
    fn pad_sha3(input: &[Boolean<E>], bitrate: usize) -> Vec<Vec<Boolean<E>>> {
        debug_assert!(bitrate > 1, "The bitrate must be greater than 1");

        // Resize the input to a multiple of 8.
        let mut padded_input = input.to_vec();
        padded_input.resize((input.len() + 7) / 8 * 8, Boolean::constant(false));

        // Step 1: Append the "0x06" byte to the message.
        padded_input.push(Boolean::constant(false));
        padded_input.push(Boolean::constant(true));
        padded_input.push(Boolean::constant(true));
        padded_input.push(Boolean::constant(false));

        // Step 2: Append "0" bits until the length of the message is congruent to r-1 mod r.
        while (padded_input.len() % bitrate) != (bitrate - 1) {
            padded_input.push(Boolean::constant(false));
        }

        // Step 3: Append the bit "1" to the message.
        padded_input.push(Boolean::constant(true));

        // Construct the padded blocks.
        let mut result = Vec::new();
        for block in padded_input.chunks(bitrate) {
            result.push(block.to_vec());
        }
        result
    }

    /// The permutation `f` is a function that takes a fixed-length input and produces a fixed-length output,
    /// defined as `f = Keccak-f[b]`, where `b := 25 * 2^l` is the width of the permutation,
    /// and `l` is the log width of the permutation.
    ///
    /// The round function `R` is applied `12 + 2l` times, where `l` is the log width of the permutation.
    fn permutation_f<const WIDTH: usize, const NUM_ROUNDS: usize>(
        input: Vec<Boolean<E>>,
        round_constants: &[U64<E>],
        rotl: &[usize],
    ) -> Vec<Boolean<E>> {
        debug_assert_eq!(input.len(), WIDTH, "The input vector must have {WIDTH} bits");

        // Partition the input into 64-bit chunks.
        let mut a = input.chunks(64).map(|e| U64::from_bits_le(e)).collect::<Vec<_>>();
        // Permute the input.
        for i in 0..NUM_ROUNDS {
            a = Self::round(a, &round_constants[i], rotl);
        }
        // Return the permuted input.
        a.into_iter().flat_map(|e| e.to_bits_le()).collect()
    }

    /// The round function `R` is defined as follows:
    /// ```text
    /// R = ι ◦ χ ◦ π ◦ ρ ◦ θ
    /// ```
    /// where `◦` denotes function composition.
    fn round(a: Vec<U64<E>>, round_constant: &U64<E>, rotl: &[usize]) -> Vec<U64<E>> {
        debug_assert_eq!(a.len(), MODULO * MODULO, "The input vector 'a' must have {} elements", MODULO * MODULO);

        const WEIGHT: usize = MODULO - 1;

        /* The first part of Algorithm 3, θ:
         *
         * for x = 0 to 4 do
         *   C[x] = a[x, 0]
         *   for y = 1 to 4 do
         *     C[x] = C[x] ⊕ a[x, y]
         *   end for
         * end for
         */
        let mut c = Vec::with_capacity(WEIGHT);
        for x in 0..MODULO {
            c.push(&a[x + 0] ^ &a[x + MODULO] ^ &a[x + (2 * MODULO)] ^ &a[x + (3 * MODULO)] ^ &a[x + (4 * MODULO)]);
        }

        /* The second part of Algorithm 3, θ:
         *
         * for x = 0 to 4 do
         *   D[x] = C[x−1] ⊕ ROT(C[x+1],1)
         *   for y = 0 to 4 do
         *     A[x, y] = a[x, y] ⊕ D[x]
         *   end for
         * end for
         */
        let mut d = Vec::with_capacity(WEIGHT);
        for x in 0..MODULO {
            d.push(&c[(x + 4) % MODULO] ^ Self::rotate_left(&c[(x + 1) % MODULO], 63));
        }
        let mut a_1 = Vec::with_capacity(WEIGHT * WEIGHT);
        for y in 0..MODULO {
            for x in 0..MODULO {
                a_1.push(&a[x + (y * MODULO)] ^ &d[x]);
            }
        }

        /* Algorithm 4, π:
         *
         * for x = 0 to 4 do
         *   for y = 0 to 4 do
         *     (X, Y) = (y, (2*x + 3*y) mod 5)
         *     A[X, Y] = a[x, y]
         *   end for
         * end for
         *
         * Algorithm 5, ρ:
         *
         * A[0, 0] = a[0, 0]
         * (x, y) = (1, 0)
         * for t = 0 to 23 do
         *   A[x, y] = ROT(a[x, y], (t + 1)(t + 2)/2)
         *   (x, y) = (y, (2*x + 3*y) mod 5)
         * end for
         */
        let mut a_2 = a_1.clone();
        for y in 0..MODULO {
            for x in 0..MODULO {
                // This step combines the π and ρ steps into one.
                a_2[y + ((((2 * x) + (3 * y)) % MODULO) * MODULO)] =
                    Self::rotate_left(&a_1[x + (y * MODULO)], rotl[x + (y * MODULO)]);
            }
        }

        /* Algorithm 2, χ:
         *
         * for y = 0 to 4 do
         *   for x = 0 to 4 do
         *     A[x, y] = a[x, y] ⊕ ((¬a[x+1, y]) ∧ a[x+2, y])
         *   end for
         * end for
         */
        let mut a_3 = Vec::with_capacity(WEIGHT * WEIGHT);
        for y in 0..MODULO {
            for x in 0..MODULO {
                let a = &a_2[x + (y * MODULO)];
                let b = &a_2[((x + 1) % MODULO) + (y * MODULO)];
                let c = &a_2[((x + 2) % MODULO) + (y * MODULO)];
                a_3.push(a ^ ((!b) & c));
            }
        }

        /* ι:
         *
         * A[0, 0] = A[0, 0] ⊕ RC
         */
        a_3[0] = &a_3[0] ^ round_constant;
        a_3
    }

    /// Performs a rotate left operation on the given `u64` value.
    fn rotate_left(value: &U64<E>, n: usize) -> U64<E> {
        // Perform the rotation.
        let bits_le = value.to_bits_le();
        let bits_le = bits_le.iter().skip(n).chain(bits_le.iter()).take(64).cloned().collect::<Vec<_>>();
        // Return the rotated value.
        U64::from_bits_le(&bits_le)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use snarkvm_circuit_types::environment::Circuit;
    use snarkvm_utilities::{bits_from_bytes_le, bytes_from_bits_le};

    use tiny_keccak::{Hasher, Keccak as TinyKeccak, Sha3 as TinySha3};

    const ITERATIONS: usize = 3;

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

    macro_rules! check_equivalence {
        ($circuit:expr, $native:expr) => {
            let rng = &mut TestRng::default();

            let mut input_sizes = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 32, 64, 128, 256, 512, 1024];
            input_sizes.extend((0..5).map(|_| u8::rand(rng) as usize));

            for num_inputs in input_sizes {
                println!("Checking equivalence for {num_inputs} inputs");

                // Prepare the preimage.
                let native_input = (0..num_inputs).map(|_| Uniform::rand(rng)).collect::<Vec<bool>>();
                let input = native_input.iter().map(|v| Boolean::<Circuit>::new(Mode::Private, *v)).collect::<Vec<_>>();

                // Compute the native hash.
                let expected = $native(&bytes_from_bits_le(&native_input));
                let expected = bits_from_bytes_le(&expected).collect::<Vec<_>>();

                // Compute the circuit hash.
                let candidate = $circuit.hash(&input);
                assert_eq!(expected, candidate.eject_value());
                Circuit::reset();
            }
        };
    }

    fn check_hash(
        mode: Mode,
        num_inputs: usize,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
        rng: &mut TestRng,
    ) {
        use console::Hash as H;

        // let native = console::Poseidon::<<Circuit as Environment>::Network, RATE>::setup(DOMAIN)?;
        let keccak = Keccak256::<Circuit>::new();

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let native_input = (0..num_inputs).map(|_| Uniform::rand(rng)).collect::<Vec<bool>>();
            let input = native_input.iter().map(|v| Boolean::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            // let expected = native.hash(&native_input).expect("Failed to hash native input");
            let expected = keccak_256_native(&bytes_from_bits_le(&native_input));
            let expected = bits_from_bytes_le(&expected).collect::<Vec<_>>();

            // Compute the circuit hash.
            Circuit::scope(format!("Keccak {mode} {i}"), || {
                let candidate = keccak.hash(&input);
                assert_eq!(expected, candidate.eject_value());
                let case = format!("(mode = {mode}, num_inputs = {num_inputs})");
                assert_scope!(case, num_constants, num_public, num_private, num_constraints);
            });
            Circuit::reset();
        }
    }

    #[test]
    fn test_keccak_256_hash_constant() {
        let mut rng = TestRng::default();

        check_hash(Mode::Constant, 1, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 2, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 3, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 4, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 5, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 6, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 7, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 8, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 16, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 32, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 64, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 128, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 256, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 511, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 512, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 513, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 1023, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 1024, 0, 0, 0, 0, &mut rng);
        check_hash(Mode::Constant, 1025, 0, 0, 0, 0, &mut rng);
    }

    #[test]
    fn test_keccak_256_hash_public() {
        let mut rng = TestRng::default();

        check_hash(Mode::Public, 1, 0, 0, 138157, 138157, &mut rng);
        check_hash(Mode::Public, 2, 0, 0, 139108, 139108, &mut rng);
        check_hash(Mode::Public, 3, 0, 0, 139741, 139741, &mut rng);
        check_hash(Mode::Public, 4, 0, 0, 140318, 140318, &mut rng);
        check_hash(Mode::Public, 5, 0, 0, 140879, 140879, &mut rng);
        check_hash(Mode::Public, 6, 0, 0, 141350, 141350, &mut rng);
        check_hash(Mode::Public, 7, 0, 0, 141787, 141787, &mut rng);
        check_hash(Mode::Public, 8, 0, 0, 142132, 142132, &mut rng);
        check_hash(Mode::Public, 16, 0, 0, 144173, 144173, &mut rng);
        check_hash(Mode::Public, 32, 0, 0, 145394, 145394, &mut rng);
        check_hash(Mode::Public, 64, 0, 0, 146650, 146650, &mut rng);
        check_hash(Mode::Public, 128, 0, 0, 149248, 149248, &mut rng);
        check_hash(Mode::Public, 256, 0, 0, 150848, 150848, &mut rng);
        check_hash(Mode::Public, 512, 0, 0, 151424, 151424, &mut rng);
        check_hash(Mode::Public, 1024, 0, 0, 152448, 152448, &mut rng);
    }

    #[test]
    fn test_keccak_256_hash_private() {
        let mut rng = TestRng::default();

        check_hash(Mode::Private, 1, 0, 0, 138157, 138157, &mut rng);
        check_hash(Mode::Private, 2, 0, 0, 139108, 139108, &mut rng);
        check_hash(Mode::Private, 3, 0, 0, 139741, 139741, &mut rng);
        check_hash(Mode::Private, 4, 0, 0, 140318, 140318, &mut rng);
        check_hash(Mode::Private, 5, 0, 0, 140879, 140879, &mut rng);
        check_hash(Mode::Private, 6, 0, 0, 141350, 141350, &mut rng);
        check_hash(Mode::Private, 7, 0, 0, 141787, 141787, &mut rng);
        check_hash(Mode::Private, 8, 0, 0, 142132, 142132, &mut rng);
        check_hash(Mode::Private, 16, 0, 0, 144173, 144173, &mut rng);
        check_hash(Mode::Private, 32, 0, 0, 145394, 145394, &mut rng);
        check_hash(Mode::Private, 64, 0, 0, 146650, 146650, &mut rng);
        check_hash(Mode::Private, 128, 0, 0, 149248, 149248, &mut rng);
        check_hash(Mode::Private, 256, 0, 0, 150848, 150848, &mut rng);
        check_hash(Mode::Private, 512, 0, 0, 151424, 151424, &mut rng);
        check_hash(Mode::Private, 1024, 0, 0, 152448, 152448, &mut rng);
    }

    #[test]
    fn test_keccak_224_equivalence() {
        check_equivalence!(Keccak224::<Circuit>::new(), keccak_224_native);
    }

    #[test]
    fn test_keccak_256_equivalence() {
        check_equivalence!(Keccak256::<Circuit>::new(), keccak_256_native);
    }

    #[test]
    fn test_keccak_384_equivalence() {
        check_equivalence!(Keccak384::<Circuit>::new(), keccak_384_native);
    }

    #[test]
    fn test_keccak_512_equivalence() {
        check_equivalence!(Keccak512::<Circuit>::new(), keccak_512_native);
    }

    #[test]
    fn test_sha3_224_equivalence() {
        check_equivalence!(Sha3_224::<Circuit>::new(), sha3_224_native);
    }

    #[test]
    fn test_sha3_256_equivalence() {
        check_equivalence!(Sha3_256::<Circuit>::new(), sha3_256_native);
    }

    #[test]
    fn test_sha3_384_equivalence() {
        check_equivalence!(Sha3_384::<Circuit>::new(), sha3_384_native);
    }

    #[test]
    fn test_sha3_512_equivalence() {
        check_equivalence!(Sha3_512::<Circuit>::new(), sha3_512_native);
    }

    #[test]
    fn test_keccak_256_simple() {
        let input = [
            91, 7, 224, 119, 168, 31, 252, 107, 71, 67, 95, 101, 168, 114, 123, 204, 84, 43, 198, 252, 15, 37, 165, 98,
            16, 239, 177, 167, 75, 136, 165, 174, 94, 93, 131, 178, 76, 70, 67, 50, 228, 244, 192, 226, 95, 102, 35,
            138, 63, 100, 209, 199, 71, 209, 21, 102, 164, 189, 160, 179, 187, 246, 232, 176,
        ];
        let output = [
            107, 59, 106, 234, 176, 69, 94, 6, 174, 161, 74, 60, 246, 41, 201, 195, 133, 117, 2, 65, 58, 246, 33, 201,
            230, 106, 98, 171, 43, 238, 105, 82,
        ];
        assert_eq!(output, keccak_256_native(&input));

        let input_circuit =
            input.to_bits_le().iter().map(|b| Boolean::<Circuit>::new(Mode::Public, *b)).collect::<Vec<_>>();

        let keccak = Keccak256::<Circuit>::new();

        let output_circuit = keccak.hash(&input_circuit);

        let output_bits_le = output.to_bits_le();

        println!("{:?}", output_bits_le);
        println!("{:?}", output_circuit);

        for (i, bit) in output_circuit.iter().enumerate() {
            assert_eq!(output_bits_le[i], bit.eject_value());
        }
    }
}
