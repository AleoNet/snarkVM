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

impl<E: Environment, const NUM_BITS: usize> Hash for Sha<E, NUM_BITS> {
    type Input = Boolean<E>;
    type Output = Field<E>;

    #[inline]
    fn hash(&self, input: &[Self::Input]) -> Self::Output {
        // Set constants
        let message_length_bits =
            (input.len() as u64).to_bits_be().into_iter().map(Boolean::<E>::constant).collect::<Vec<_>>();
        let chunk_size = NUM_BITS * 2;

        // Pad Message with 1 bit
        let mut input = Cow::Borrowed(input);
        let padded_length = input.len() + 1;
        input.to_mut().resize(padded_length, Boolean::constant(true));

        // Determine how many zeros we need to pad the message with
        let chunks = padded_length / chunk_size + 1;
        let remaining_bits_length = chunks * NUM_BITS - padded_length;
        let extension_bit_length = if remaining_bits_length >= 64 {
            remaining_bits_length - 64
        } else {
            remaining_bits_length + NUM_BITS - 64
        };
        input.to_mut().resize(padded_length + extension_bit_length, Boolean::constant(false));
        input.to_mut().extend(message_length_bits);
        match NUM_BITS {
            256 => {
                let (mut state, round_constants, rotation_constants) = (
                    Self::constants::<u32>(STATE_256),
                    Self::constants::<u32>(ROUND_256),
                    Self::constants::<u8>(ROTATION_256),
                );
                Self::sha::<u32>(
                    input.to_mut().as_mut_slice(),
                    state.as_mut_slice(),
                    &round_constants,
                    &rotation_constants,
                )
            }
            512 => {
                let (mut state, round_constants, rotation_constants) = (
                    Self::constants::<u64>(STATE_512),
                    Self::constants::<u64>(ROUND_512),
                    Self::constants::<u8>(ROTATION_512),
                );
                Self::sha::<u64>(
                    input.to_mut().as_mut_slice(),
                    state.as_mut_slice(),
                    &round_constants,
                    &rotation_constants,
                )
            }
            _ => E::halt("Invalid hash size"),
        }
    }
}

impl<E: Environment, const NUM_BITS: usize> Sha<E, NUM_BITS> {
    #[inline]
    pub fn sha<I: IntegerType>(
        input: &[Boolean<E>],
        state: &mut [Integer<E, I>],
        round_constants: &[Integer<E, I>],
        rotation_constants: &[U8<E>],
    ) -> Field<E> {
        let chunk_size = NUM_BITS * 2;
        let word_size = NUM_BITS / 8;
        // Initialize schedule array
        for chunk in input.chunks_exact(chunk_size) {
            let mut vec = vec![];
            for word in chunk.chunks_exact(word_size) {
                vec.push(Integer::<E, I>::from_bits_be(word));
            }
            let array_start = vec.len();
            vec.extend(vec![Integer::<E, I>::zero(); Self::schedule_array_size() - array_start]);

            for i in array_start..Self::schedule_array_size() {
                let s0 = vec[i - 15].shr_wrapped(&rotation_constants[0])
                    ^ vec[i - 15].shr_wrapped(&rotation_constants[1])
                    ^ vec[i - 15].shr_checked(&rotation_constants[2]);
                let s1 = vec[i - 2].shr_wrapped(&rotation_constants[3])
                    ^ vec[i - 2].shr_wrapped(&rotation_constants[4])
                    ^ vec[i - 2].shr_checked(&rotation_constants[5]);
                vec[i] = &vec[i - 16] + s0 + &vec[i - 7] + s1;
            }

            let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) = (
                state[0].clone(),
                state[1].clone(),
                state[2].clone(),
                state[3].clone(),
                state[4].clone(),
                state[5].clone(),
                state[6].clone(),
                state[7].clone(),
            );

            for i in 0..Self::schedule_array_size() {
                let s1 = &e.shr_wrapped(&rotation_constants[6])
                    ^ &e.shr_wrapped(&rotation_constants[7])
                    ^ &e.shr_wrapped(&rotation_constants[8]);
                let ch = (&e & &f) ^ ((!&e) & &g);
                let temp1 = &h + &s1 + &ch + &round_constants[i] + &vec[i];
                let s0 = &a.shr_wrapped(&rotation_constants[9])
                    ^ &a.shr_wrapped(&rotation_constants[10])
                    ^ &a.shr_wrapped(&rotation_constants[11]);
                let maj = (&a & &b) ^ (&a & &c) ^ (&b & &c);
                let temp2 = s0 + maj;

                h = g;
                g = f;
                f = e;
                e = d + temp1.clone();
                d = c;
                c = b;
                b = a;
                a = temp1 + temp2;
            }

            state[0] = a + &state[0];
            state[1] = b + &state[1];
            state[2] = c + &state[2];
            state[3] = d + &state[3];
            state[4] = e + &state[4];
            state[5] = f + &state[5];
            state[6] = g + &state[6];
            state[7] = h + &state[7];
        }

        let bytes = state.iter_mut().flat_map(|s| s.to_bits_be()).collect::<Vec<_>>();
        Field::from_bits_be(&bytes)
    }
}
