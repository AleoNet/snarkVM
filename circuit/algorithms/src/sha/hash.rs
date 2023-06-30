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
use snarkvm_circuit_types::environment::Circuit;

impl<E: Environment, const NUM_BITS: usize> HashMany for Sha<E, NUM_BITS> {
    type Input = Boolean<E>;
    type Output = U8<E>;

    #[inline]
    fn hash_many(&self, input: &[Self::Input], _num_outputs: u16) -> Vec<Self::Output> {
        let mut input = Self::pad_message::<u8>(input);

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
    fn pad_message<I: IntegerType>(input: &[Boolean<E>]) -> Cow<[Boolean<E>]> {
        // Set constants
        let message_length_bits =
            U64::<E>::new(Mode::Constant, console::Integer::<E::Network, u64>::new(input.len() as u64));
        let chunk_size = NUM_BITS * 2;

        // Pad Message with 1 bit
        let mut input = Cow::Borrowed(input);
        let padded_length = input.len() + 1;
        input.to_mut().push(Boolean::constant(true));

        // Determine how many zeros we need to pad the message with
        let chunks = padded_length / chunk_size + 1;
        let remaining_bits_length = chunks * chunk_size - padded_length;
        let extension_bit_length = if remaining_bits_length >= 64 {
            remaining_bits_length - 64
        } else {
            remaining_bits_length + chunk_size - 64
        };

        // Pad Message with 0 bits and message length until we reach a multiple of 512 bits
        input.to_mut().extend(vec![Boolean::constant(false); extension_bit_length]);
        input.to_mut().extend(message_length_bits.to_bits_be());
        input
    }

    #[inline]
    fn right_rotate<I: IntegerType>(x: &Integer<E, I>, shift: &U8<E>) -> Integer<E, I> {
        // Calculate rotation mask
        let bits = match NUM_BITS {
            256 => U8::<E>::constant(console::Integer::<<E as Environment>::Network, u8>::new(32u8)),
            512 => U8::<E>::constant(console::Integer::<<E as Environment>::Network, u8>::new(64u8)),
            _ => E::halt("Invalid hash size"),
        };
        let one = Integer::<E, I>::one();
        let mask = (&one << shift) - one;

        // Apply mask and right rotate bits
        let shifted_bits = x & mask;
        (x >> shift) | (shifted_bits << &(bits - shift))
    }

    #[inline]
    pub fn sha<I: IntegerType>(
        input: &[Boolean<E>],
        state: &mut [Integer<E, I>],
        round_constants: &[Integer<E, I>],
        rotation_constants: &[U8<E>],
    ) -> Vec<U8<E>> {
        let chunk_size = NUM_BITS * 2;
        let word_size = NUM_BITS / 8;

        // Initialize schedule array
        for chunk in input.chunks_exact(chunk_size) {
            // Put first 16 values into array
            let mut schedule_array = vec![];
            for word in chunk.chunks_exact(word_size) {
                schedule_array.push(Integer::<E, I>::from_bits_be(word));
            }
            println!("schedule_array: {:?}", schedule_array);
            let array_start = schedule_array.len();
            schedule_array.extend(vec![Integer::<E, I>::zero(); Self::schedule_array_size() - array_start]);

            for i in array_start..Self::schedule_array_size() {
                let s0 = Self::right_rotate(&schedule_array[i - 15], &rotation_constants[0])
                    ^ Self::right_rotate(&schedule_array[i - 15], &rotation_constants[1])
                    ^ (&schedule_array[i - 15] >> (&rotation_constants[2]));
                let s1 = Self::right_rotate(&schedule_array[i - 2], &rotation_constants[3])
                    ^ Self::right_rotate(&schedule_array[i - 2], &rotation_constants[4])
                    ^ (&schedule_array[i - 2] >> &rotation_constants[5]);
                schedule_array[i] =
                    s1.add_wrapped(&schedule_array[i - 7]).add_wrapped(&s0).add_wrapped(&schedule_array[i - 16]);
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
                let s1 = Self::right_rotate(&e, &rotation_constants[6])
                    ^ Self::right_rotate(&e, &rotation_constants[7])
                    ^ Self::right_rotate(&e, &rotation_constants[8]);
                let ch = (&e & &f) ^ ((!&e) & &g);
                let temp1 = &h + &s1 + &ch + &round_constants[i] + &schedule_array[i];
                let s0 = Self::right_rotate(&a, &rotation_constants[9])
                    ^ Self::right_rotate(&a, &rotation_constants[10])
                    ^ Self::right_rotate(&a, &rotation_constants[11]);
                let maj = (&a & &b) ^ (&a & &c) ^ (&b & &c);
                let temp2 = s0.add_wrapped(&maj);

                h = g;
                g = f;
                f = e;
                e = d + &temp1;
                d = c;
                c = b;
                b = a;
                a = temp1 + temp2;
            }

            state[0] += a;
            state[1] += b;
            state[2] += c;
            state[3] += d;
            state[4] += e;
            state[5] += f;
            state[6] += g;
            state[7] += h;
        }

        let digest = state.iter().flat_map(|s| s.to_bits_be()).collect::<Vec<_>>();
        digest.chunks(8).map(U8::<E>::from_bits_be).collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use snarkvm_circuit_types::environment::Circuit;

    const SHA256_OF_256U64_AS_LE_BYTES: &[u8] = &[
        46, 34, 253, 67, 80, 96, 205, 93, 60, 245, 227, 239, 57, 247, 158, 25, 139, 53, 189, 44, 74, 243, 25, 116, 219,
        54, 96, 27, 58, 47, 76, 145,
    ];

    #[test]
    fn sha256_hash_matches() {
        let sha = Sha256::<Circuit>::default();
        let input = console::Integer::<<Circuit as Environment>::Network, u64>::new(256u64);
        let circuit_input = Integer::<Circuit, u64>::new(Mode::Public, input);
        let hash = sha.hash_many(&circuit_input.to_bits_le(), 5);
        println!("Result: {:?}", hash);
    }
}
