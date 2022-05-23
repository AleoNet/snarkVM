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

#![allow(dead_code)]

use crate::{FieldParameters, PrimeField};
use snarkvm_utilities::{cmp::Ordering, vec::Vec, FromBits};

use anyhow::{bail, Result};

pub struct PoseidonGrainLFSR {
    pub field_size_in_bits: u64,
    pub state: [bool; 80],
    pub head: usize,
}

impl PoseidonGrainLFSR {
    pub fn new(
        is_sbox_an_inverse: bool,
        field_size_in_bits: u64,
        state_len: u64,
        num_full_rounds: u64,
        num_partial_rounds: u64,
    ) -> Self {
        let mut state = [false; 80];

        // b0, b1 describes the field
        state[1] = true;

        // b2, ..., b5 describes the S-BOX
        if is_sbox_an_inverse {
            state[5] = true;
        } else {
            state[5] = false;
        }

        // b6, ..., b17 are the binary representation of n (prime_num_bits)
        {
            let mut cur = field_size_in_bits;
            for i in (6..=17).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        // b18, ..., b29 are the binary representation of t (state_len, rate + capacity)
        {
            let mut cur = state_len;
            for i in (18..=29).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        // b30, ..., b39 are the binary representation of R_F (the number of full rounds)
        {
            let mut cur = num_full_rounds;
            for i in (30..=39).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        // b40, ..., b49 are the binary representation of R_P (the number of partial rounds)
        {
            let mut cur = num_partial_rounds;
            for i in (40..=49).rev() {
                state[i] = cur & 1 == 1;
                cur >>= 1;
            }
        }

        #[allow(clippy::needless_range_loop)]
        // b50, ..., b79 are set to 1
        for i in 50..=79 {
            state[i] = true;
        }

        // Initialize.
        let mut res = Self { field_size_in_bits, state, head: 0 };
        for _ in 0..160 {
            res.next_bit();
        }
        res
    }

    pub fn get_field_elements_rejection_sampling<F: PrimeField>(&mut self, num_elements: usize) -> Result<Vec<F>> {
        // Ensure the number of bits matches the modulus.
        if self.field_size_in_bits != F::Parameters::MODULUS_BITS as u64 {
            bail!("The number of bits in the field must match the modulus");
        }

        let mut output = Vec::with_capacity(num_elements);
        for _ in 0..num_elements {
            // Perform rejection sampling.
            loop {
                // Obtain `n` bits and make it most-significant-bit first.
                let bits = self.get_bits(self.field_size_in_bits as usize);
                // Construct the number.
                let bigint = F::BigInteger::from_bits_be(&bits)?;
                // Ensure the number is in the field.
                if bigint.cmp(&F::Parameters::MODULUS) == Ordering::Less {
                    if let Some(element) = F::from_repr(bigint) {
                        output.push(element);
                        break;
                    }
                }
            }
        }
        Ok(output)
    }

    pub fn get_field_elements_mod_p<F: PrimeField>(&mut self, num_elems: usize) -> Result<Vec<F>> {
        // Ensure the number of bits matches the modulus.
        if self.field_size_in_bits != F::Parameters::MODULUS_BITS as u64 {
            bail!("The number of bits in the field must match the modulus");
        }

        let mut output = Vec::with_capacity(num_elems);
        for _ in 0..num_elems {
            // Obtain `n` bits and make it most-significant-bit first.
            let mut bits = self.get_bits(self.field_size_in_bits as usize);
            bits.reverse();

            let bytes = bits
                .chunks(8)
                .map(|chunk| {
                    let mut sum = chunk[0] as u8;
                    let mut cur = 1;
                    for i in chunk.iter().skip(1) {
                        cur *= 2;
                        sum += cur * (*i as u8);
                    }
                    sum
                })
                .rev()
                .collect::<Vec<u8>>();

            output.push(F::from_bytes_be_mod_order(&bytes));
        }
        Ok(output)
    }
}

impl PoseidonGrainLFSR {
    #[inline]
    fn get_bits(&mut self, num_bits: usize) -> Vec<bool> {
        let mut bits = Vec::with_capacity(num_bits);

        for _ in 0..num_bits {
            // Obtain the first bit
            let mut new_bit = self.next_bit();

            // Loop until the first bit is true
            while !new_bit {
                // Discard the second bit
                let _ = self.next_bit();
                // Obtain another first bit
                new_bit = self.next_bit();
            }

            // Obtain the second bit
            bits.push(self.next_bit());
        }

        bits
    }

    #[inline]
    fn next_bit(&mut self) -> bool {
        let next_bit = self.state[(self.head + 62) % 80]
            ^ self.state[(self.head + 51) % 80]
            ^ self.state[(self.head + 38) % 80]
            ^ self.state[(self.head + 23) % 80]
            ^ self.state[(self.head + 13) % 80]
            ^ self.state[self.head];
        self.state[self.head] = next_bit;
        self.head += 1;
        self.head %= 80;

        next_bit
    }
}
