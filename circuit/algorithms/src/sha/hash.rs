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
use crate::sha::constants::*;
use snarkvm_circuit_types::environment::circuit;
use snarkvm_circuit_types::integers::Integer;

const BIT_SIZE: usize = Sha::bit_size();

impl<E: Environment, const NUM_BITS: usize> Hash for Sha<E, NUM_BITS> {
    type Input = Boolean<E>;
    type Output = Field<E>;

    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        // Set constants
        let message_length =
            (input.len() as u64).to_bits_be().into_iter().map(|b| Boolean::<E>::constant(b)).collect::<Vec<_>>();
        let chunk_size = NUM_BITS * 2;
        let word_size = 32;

        // Pad Message with 1 bit
        let mut input = Cow::Borrowed(input);
        let padded_length = input.len() + 1;
        input.to_mut().resize(padded_length, Boolean::constant(true));

        // Determine how many zeros we need to pad the message with
        let chunks = padded_length / chunk_size + 1;
        let remaining_bits = chunks * NUM_BITS - padded_length;
        let extension_bits = if remaining_bits >= 64 { remaining_bits - 64 } else { remaining_bits + NUM_BITS - 64 };
        input.to_mut().resize(padded_length + extension_bits, Boolean::constant(false));
        input.to_mut().extend(message_length);

        // Initialize state
        let (mut state, round_constants) = Self::round_constants();
        let rotation_constants = Self::rotation_constants();

        // Initialize schedule array
        for chunk in input.chunks_exact(chunk_size) {
            let mut vec = vec![];
            for (i, other) in chunk.chunks_exact(word_size).enumerate() {
                vec.push(Integer::<E, bit_size!(NUM_BITS)>::from_bits_be(other));
            }
            let array_start = Self::schedule_array_size() - vec.len();
            vec.extend(vec![initialize!(NUM_BITS); array_start]);
            for i in array_start..Self::schedule_array_size() {
                let s0 = vec[i - 15].shr_wrapped(&rotation_constants[0]) ^ vec[i - 15].shr_wrapped(&rotation_constants[1]) ^ vec[i - 15].shr_checked(&rotation_constants[2]);
                let s1 = vec[i - 2].shr_wrapped(&rotation_constants[3]) ^ vec[i - 2].shr_wrapped(&rotation_constants[4]) ^ vec[i - 2].shr_checked(&rotation_constants[5]);
                vec[i] = *vec[i - 16] + s0 + *vec[i - 7] + s1;
            }

            let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) = (*state[0], *state[1], *state[2], *state[3], *state[4], *state[5], *state[6], *state[7]);

            for i in 0..Self::schedule_array_size() {
                let s1 = e.shr_wrapped(&rotation_constants[6]) ^ e.shr_wrapped(&rotation_constants[7]) ^ e.shr_wrapped(&rotation_constants[8]);
                let ch = (e & f) ^ ((!e) & g);
                let temp1 = h + s1 + ch + *round_constants[i] + *vec[i];
                let s0 = a.shr_wrapped(&rotation_constants[9]) ^ a.shr_wrapped(&rotation_constants[10]) ^ a.shr_wrapped(&rotation_constants[11]);
                let maj = (a & b) ^ (a & c) ^ (b & c);
                let temp2 = s0 + maj;

                let h = g;
                let g = f;
                let f = e;
                let e = d + temp1;
                let d = c;
                let c = b;
                let b = a;
                let a = temp1 + temp2;
            }

            state[0] = a + *state[0];
            state[1] = b + *state[1];
            state[2] = c + *state[2];
            state[3] = d + *state[3];
            state[4] = e + *state[4];
            state[5] = f + *state[5];
            state[6] = g + *state[6];
            state[7] = h + *state[7];
        }

        let bytes = state.into_iter().flat_map(|s| s.to_bits_be()).collect::<Vec<_>>();
        Field::from_bits_be(&bytes)
    }
}

impl<E: Environment, const NUM_BITS: usize> Sha<E, NUM_BITS> {
    #[inline]
    const fn schedule_array_size() -> usize {
        match NUM_BITS {
            256 => 64,
            512 => 80,
            _ => E::halt("Invalid hash size"),
        }
    }

    #[inline]
    const fn round_constants() -> (Vec<Integer<E, bit_size!(NUM_BITS)>>, Vec<Integer<E, bit_size!(NUM_BITS)>>) {
        match NUM_BITS {
            256 => (sha256_initial_state(), sha256_round_constants()),
            512 => (sha512_initial_state(), sha512_round_constants()),
            _ => E::halt("Invalid hash size"),
        }
    }

    #[inline]
    const fn schedule_constants() -> (Vec<Integer<E, bit_size!(NUM_BITS)>>, Vec<Integer<E, bit_size!(NUM_BITS)>>) {
        match NUM_BITS {
            256 => (Integer::<E, bit_size!(NUM_BITS)>::),
            512 => (sha512_initial_state(), sha512_round_constants()),
            _ => E::halt("Invalid hash size"),
        }
    }

    #[inline]
    const fn rotation_constants() -> Vec<Integer<E, bit_size!(NUM_BITS)>> {
        match NUM_BITS {
            256 => sha256_rotation_constants(),
            512 => sha512_rotation_constants(),
            _ => E::halt("Invalid hash size"),
        }
    }
}

#[macro_export]
macro_rules! bit_size {
    (256) => {
        u32
    };
    (512) => {
        u64
    };
    ($n:literal) => {
        $E::halt("Invalid hash size")
    };
}

macro_rules! initialize {
    (256) => {
        U32::zero()
    };
    (512) => {
        U64::zero()
    };
    ($n:literal) => {
        $E::halt("Invalid hash size")
    };
}
