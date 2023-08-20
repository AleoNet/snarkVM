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

/// The rows and columns are 5 bits.
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
/// In SHA-3, `pad` is a SHAKE or cSHAKE (for XOF) padding, defined as `pad(M) = M || 0x01 || 0x00…0x00`,
/// where `M` is the input data, and `0x01 || 0x00…0x00` is the padding.
///
/// The bitrate `r` is the number of bits that are absorbed into the sponge state in each iteration
/// of the absorbing phase.
/// For our case, `r = 1088`.
///
/// In addition, the capacity is defined as `c := b - r`. For our case, `c = 512`, as `b = 1600` and `r = 1088`.
pub struct Keccak<E: Environment> {
    /// The round constants `RC[t] ∈ GF(2)` are defined as the
    /// output of a linear feedback shift register (LFSR).
    round_constants: Vec<U64<E>>,
    /// Precomputations for the ρ step.
    rotl: Vec<usize>,
}

impl<E: Environment> Keccak<E> {
    /// Initializes a new Keccak hash function.
    pub fn new() -> Self {
        Self {
            round_constants: Self::ROUND_CONSTANTS.into_iter().map(|e| U64::constant(console::U64::new(e))).collect(),
            rotl: Self::rotl_offsets::<NUM_ROUNDS>(),
        }
    }
}

impl<E: Environment> Hash for Keccak<E> {
    type Input = Boolean<E>;
    type Output = Vec<Boolean<E>>;

    /// Returns the Keccak-256 hash of the given input as bits.
    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        /// The capacity `c`.
        const CAPACITY: usize = 512;
        /// The permutation width `b`.
        const PERMUTATION_WIDTH: usize = 1600;
        /// The bitrate `r`.
        const BITRATE: usize = PERMUTATION_WIDTH - CAPACITY;
        /// The output length `l`.
        const OUTPUT_LENGTH: usize = 256;

        debug_assert!(BITRATE < PERMUTATION_WIDTH, "The bitrate must be less than the permutation width");

        // The padded blocks `P`.
        let padded_blocks = Self::pad_keccak::<PERMUTATION_WIDTH>(input, CAPACITY, BITRATE);

        // The root state `s` is defined as `0^b`.
        let mut s = vec![Boolean::constant(false); PERMUTATION_WIDTH];

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
        let mut z = s[..BITRATE].to_vec();
        // while |Z|_r < l do
        while z.len() < OUTPUT_LENGTH {
            // s = f(s)
            s = Self::permutation_f::<PERMUTATION_WIDTH, NUM_ROUNDS>(s, &self.round_constants, &self.rotl);
            // Z = Z || s[0..r-1]
            z.extend(s.iter().take(BITRATE).cloned());
        }
        // return Z[0..l-1]
        z.into_iter().take(OUTPUT_LENGTH).collect()
    }
}

impl<E: Environment> Keccak<E> {
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
    fn pad_keccak<const WIDTH: usize>(input: &[Boolean<E>], capacity: usize, bitrate: usize) -> Vec<Vec<Boolean<E>>> {
        debug_assert_eq!(bitrate, WIDTH - capacity, "The bitrate must be less than the permutation width");
        // Initialize a vector to store the padded blocks.
        let mut result = Vec::with_capacity(input.len() / capacity);
        // Iterate over the input in `capacity` chunks.
        for block in input.chunks(capacity) {
            // Construct the padded block.
            let mut m = block.to_vec();
            m.push(Boolean::constant(true));
            m.resize(WIDTH, Boolean::constant(false));
            m[bitrate - 1] = Boolean::constant(true);
            // Append the padded block to the result.
            result.push(m);
        }
        // Return the result.
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

    use tiny_keccak::{Hasher, Keccak as TinyKeccak};

    const ITERATIONS: usize = 10;

    /// Computes the Keccak-256 hash of the given preimage as bytes.
    fn keccak256_native(preimage: &[u8]) -> [u8; 32] {
        let mut keccak = TinyKeccak::v256();
        keccak.update(preimage);

        let mut hash = [0u8; 32];
        keccak.finalize(&mut hash);
        hash
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
        let keccak = Keccak::<Circuit>::new();

        for i in 0..ITERATIONS {
            // Prepare the preimage.
            let native_input = (0..num_inputs).map(|_| Uniform::rand(rng)).collect::<Vec<bool>>();
            let input = native_input.iter().map(|v| Boolean::<Circuit>::new(mode, *v)).collect::<Vec<_>>();

            // Compute the native hash.
            // let expected = native.hash(&native_input).expect("Failed to hash native input");
            let expected = keccak256_native(&bytes_from_bits_le(&native_input));
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

    // #[test]
    // fn test_hash_constant() -> Result<()> {
    //     let mut rng = TestRng::default();
    //
    //     for num_inputs in 0..=RATE {
    //         check_hash(Mode::Constant, num_inputs, 1, 0, 0, 0, &mut rng)?;
    //     }
    //     Ok(())
    // }

    // #[test]
    // fn test_hash_public() -> Result<()> {
    //     let mut rng = TestRng::default();
    //
    //     check_hash(Mode::Public, 0, 1, 0, 0, 0, &mut rng)?;
    //     check_hash(Mode::Public, 1, 1, 0, 335, 335, &mut rng)?;
    //     check_hash(Mode::Public, 2, 1, 0, 340, 340, &mut rng)?;
    //     check_hash(Mode::Public, 3, 1, 0, 345, 345, &mut rng)?;
    //     check_hash(Mode::Public, 4, 1, 0, 350, 350, &mut rng)?;
    //     check_hash(Mode::Public, 5, 1, 0, 705, 705, &mut rng)?;
    //     check_hash(Mode::Public, 6, 1, 0, 705, 705, &mut rng)?;
    //     check_hash(Mode::Public, 7, 1, 0, 705, 705, &mut rng)?;
    //     check_hash(Mode::Public, 8, 1, 0, 705, 705, &mut rng)?;
    //     check_hash(Mode::Public, 9, 1, 0, 1060, 1060, &mut rng)?;
    //     check_hash(Mode::Public, 10, 1, 0, 1060, 1060, &mut rng)
    // }

    #[test]
    fn test_hash_private() {
        let mut rng = TestRng::default();

        // check_hash(Mode::Private, 32, 0, 0, 145394, 145394, &mut rng);
        // check_hash(Mode::Private, 64, 0, 0, 146650, 146650, &mut rng);
        check_hash(Mode::Private, 512, 0, 0, 151424, 151424, &mut rng);
        // check_hash(Mode::Private, 1024, 0, 0, 151424, 151424, &mut rng);
        // check_hash(Mode::Private, 0, 1, 0, 0, 0, &mut rng);
        // check_hash(Mode::Private, 2, 1, 0, 340, 340, &mut rng)?;
        // check_hash(Mode::Private, 3, 1, 0, 345, 345, &mut rng)?;
        // check_hash(Mode::Private, 4, 1, 0, 350, 350, &mut rng)?;
        // check_hash(Mode::Private, 5, 1, 0, 705, 705, &mut rng)?;
        // check_hash(Mode::Private, 6, 1, 0, 705, 705, &mut rng)?;
        // check_hash(Mode::Private, 7, 1, 0, 705, 705, &mut rng)?;
        // check_hash(Mode::Private, 8, 1, 0, 705, 705, &mut rng)?;
        // check_hash(Mode::Private, 9, 1, 0, 1060, 1060, &mut rng)?;
        // check_hash(Mode::Private, 10, 1, 0, 1060, 1060, &mut rng)
    }

    #[test]
    fn test_keccak256_simple() {
        let input = [
            91, 7, 224, 119, 168, 31, 252, 107, 71, 67, 95, 101, 168, 114, 123, 204, 84, 43, 198, 252, 15, 37, 165, 98,
            16, 239, 177, 167, 75, 136, 165, 174, 94, 93, 131, 178, 76, 70, 67, 50, 228, 244, 192, 226, 95, 102, 35,
            138, 63, 100, 209, 199, 71, 209, 21, 102, 164, 189, 160, 179, 187, 246, 232, 176,
        ];
        let output = [
            107, 59, 106, 234, 176, 69, 94, 6, 174, 161, 74, 60, 246, 41, 201, 195, 133, 117, 2, 65, 58, 246, 33, 201,
            230, 106, 98, 171, 43, 238, 105, 82,
        ];
        assert_eq!(output, keccak256_native(&input));

        let input_circuit =
            input.to_bits_le().iter().map(|b| Boolean::<Circuit>::new(Mode::Public, *b)).collect::<Vec<_>>();

        let keccak = Keccak::<Circuit>::new();

        let output_circuit = keccak.hash(&input_circuit);

        let output_bits_le = output.to_bits_le();

        println!("{:?}", output_bits_le);
        println!("{:?}", output_circuit);

        for (i, bit) in output_circuit.iter().enumerate() {
            assert_eq!(output_bits_le[i], bit.eject_value());
        }
    }
}
