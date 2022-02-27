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

///!
///! Blake2Xs function
///!
///! This implementation is based on the BLAKE2Xs specification in Section 2 of
///! <https://www.blake2.net/blake2x.pdf>
///!

#[rustfmt::skip]
#[macro_export]
macro_rules! const_assert {
    ($x:expr $(,)*) => {
        pub const ASSERT: [(); 1] = [()];
        pub const fn bool_assert(x: bool) -> bool { x }
        let _ = ASSERT[!bool_assert($x) as usize];
    };
}

/// Converts a string of 8 characters into a `u64` for personalization in Blake2Xs.
#[macro_export]
macro_rules! personalization {
    ( $persona: expr ) => {{
        // panic!("Personalization must be exactly 8 characters")
        const_assert!($persona.len() == 8);
        let p = $persona.as_bytes();
        u64::from_le_bytes([p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]])
    }};
}

pub struct Blake2Xs;

impl Blake2Xs {
    /// Returns the BLAKE2Xs digest given:
    ///  - `input` is an input message as a slice of bytes,
    ///  - `XOF_DIGEST_LENGTH` is a `u16` set to the length of the final output digest in bytes,
    ///  - `PERSONALIZATION` is a `u64` representing a UTF-8 string of 8 characters.
    pub fn evaluate(input: &[u8], xof_digest_length: u16, persona: &[u8]) -> Vec<u8> {
        debug_assert!(xof_digest_length > 0, "Output digest must be of non-zero length");
        debug_assert!(persona.len() <= 8, "Personalization may be at most 8 characters");

        // Start by computing the digest of the input bytes.
        let xof_digest_length_node_offset = (xof_digest_length as u64) << 32;
        let input_digest = blake2s_simd::Params::new()
            .hash_length(32)
            .node_offset(xof_digest_length_node_offset)
            .personal(persona)
            .hash(input);

        let mut output = vec![];

        let num_rounds = (xof_digest_length + 31) / 32;
        for node_offset in 0..num_rounds {
            // Calculate the digest length for this round.
            let is_final_round = node_offset == num_rounds - 1;
            let has_remainder = xof_digest_length % 32 != 0;
            let digest_length = match is_final_round && has_remainder {
                true => (xof_digest_length % 32) as usize,
                false => 32,
            };

            // Compute the next part of the output digest.
            output.extend_from_slice(
                blake2s_simd::Params::new()
                    .hash_length(digest_length)
                    .fanout(0)
                    .max_depth(0)
                    .max_leaf_length(32)
                    .node_offset(xof_digest_length_node_offset | (node_offset as u64))
                    .inner_hash_length(32)
                    .personal(persona)
                    .hash(input_digest.as_bytes())
                    .as_bytes(),
            );
        }

        output
    }
}

#[cfg(test)]
mod tests {
    use crate::crypto_hash::Blake2Xs;
    use serde::Deserialize;

    #[derive(Deserialize)]
    struct Case {
        hash: String,
        #[serde(rename = "in")]
        input: String,
        key: String,
        #[serde(rename = "out")]
        output: String,
    }

    #[test]
    fn test_aleo_personalization() {
        const ALEO_PERSONA: u64 = personalization!("AleoB2Xs");

        assert_eq!(8311448373230398529, ALEO_PERSONA);
        assert_eq!(ALEO_PERSONA, u64::from_le_bytes(ALEO_PERSONA.to_le_bytes()));
        assert_eq!([65, 108, 101, 111, 66, 50, 88, 115], ALEO_PERSONA.to_le_bytes());
        assert_eq!("AleoB2Xs".as_bytes(), ALEO_PERSONA.to_le_bytes());
        assert_eq!("AleoB2Xs", std::str::from_utf8(&ALEO_PERSONA.to_le_bytes()).unwrap());
    }

    #[test]
    fn test_blake2xs() {
        // Run test vector cases.
        let vectors: Vec<Case> = serde_json::from_str(include_str!("./resources/blake2-kat.json")).unwrap();
        for case in vectors.iter().filter(|v| &v.hash == "blake2xs" && v.key.is_empty()) {
            let input = hex::decode(case.input.as_bytes()).unwrap();
            let xof_digest_length = case.output.len() as u16 / 2;
            let output = hex::encode(Blake2Xs::evaluate(&input, xof_digest_length, "".as_bytes()));
            assert_eq!(output, case.output);
        }
    }

    #[test]
    fn test_blake2s() {
        // Run test vector cases for blake2s as a sanity check for the underlying impl.
        let vectors: Vec<Case> = serde_json::from_str(include_str!("./resources/blake2-kat.json")).unwrap();
        for case in vectors.iter().filter(|v| &v.hash == "blake2s" && v.key.is_empty()) {
            let input = hex::decode(case.input.as_bytes()).unwrap();
            let output = hex::encode(blake2s_simd::Params::new().personal(&0u64.to_le_bytes()).hash(&input).as_bytes());
            assert_eq!(output, case.output);
        }
    }
}
