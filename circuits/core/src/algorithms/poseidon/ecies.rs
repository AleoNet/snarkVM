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

use super::*;

use snarkvm_circuits_environment::prelude::*;
use snarkvm_circuits_types::prelude::*;
use snarkvm_fields::PrimeField;

/// ECIESPoseidonEncryption is an encryption gadget which uses Poseidon under the hood.
pub struct ECIESPoseidonEncryption<E: Environment, const RATE: usize> {
    poseidon: Poseidon<E, RATE>,
    symmetric_encryption_domain: Field<E>,
}

impl<E: Environment, const RATE: usize> ECIESPoseidonEncryption<E, RATE> {
    /// Initializes a new instance of the ECIES gadget with the given setup message.
    pub fn setup() -> Self {
        let poseidon = Poseidon::<E, RATE>::new();
        let symmetric_encryption_domain =
            Field::constant(E::BaseField::from_bytes_le_mod_order(b"AleoSymmetricEncryption0"));

        Self { poseidon, symmetric_encryption_domain }
    }

    /// Encode a bitstring into a vector of field elements. This is used to convert messages
    /// to hashable [`Field`] elements.
    pub fn encode_message(&self, message: &[Boolean<E>]) -> Vec<Field<E>> {
        // Add an extra bit to the message.
        // The final bit serves as a terminus indicator,
        // and is used during decryption to ensure the length is correct.
        let mut bits = message.to_vec();
        bits.push(Boolean::constant(true));

        // Pack the bits into field elements.
        bits.chunks(E::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
    }

    /// Decode a vector of field elements to a bitstring. This is used to convert back from
    /// hashable [`Field`] elements to a normal message.
    pub fn decode_message(&self, encoded_message: &[Field<E>]) -> Vec<Boolean<E>> {
        let capacity = E::BaseField::size_in_data_bits();

        let mut bits = Vec::<Boolean<E>>::with_capacity(encoded_message.len() * capacity);
        for element in encoded_message.iter() {
            bits.extend_from_slice(&element.to_bits_le()[..capacity]);
        }

        // Drop all the ending zeros and the last "1" bit.
        // Note that there must be at least one "1" bit because the last element is not zero.
        loop {
            if bits.pop().unwrap().eject_value() {
                break;
            }
        }

        if bits.len() % 8 != 0 {
            E::halt("The number of bits in the packed field elements is not a multiple of 8.")
        } else {
            bits
        }
    }

    /// Symmetrically encrypt a string of plaintext, using a given symmetric key.
    pub fn encrypt(&self, symmetric_key: Field<E>, message: &[Field<E>]) -> Vec<Field<E>> {
        let randomizers =
            self.poseidon.hash_many(&[self.symmetric_encryption_domain.clone(), symmetric_key], message.len());

        message.iter().zip_eq(randomizers).map(|(plaintext, randomizer)| plaintext + randomizer).collect()
    }

    /// Decrypt a ciphertext with the given symmetric key.
    pub fn decrypt(&self, symmetric_key: Field<E>, ciphertext: &[Field<E>]) -> Vec<Field<E>> {
        let randomizers =
            self.poseidon.hash_many(&[self.symmetric_encryption_domain.clone(), symmetric_key], ciphertext.len());

        ciphertext.iter().zip_eq(randomizers).map(|(ciphertext, randomizer)| ciphertext - &randomizer).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_algorithms::{encryption::ECIESPoseidonEncryption as NativeECIES, EncryptionScheme};
    use snarkvm_circuits_environment::Circuit;
    use snarkvm_curves::{
        edwards_bls12::{EdwardsAffine, EdwardsParameters},
        AffineCurve,
    };
    use snarkvm_utilities::{test_rng, UniformRand};

    const ITERATIONS: u64 = 10;
    const MESSAGE: &str = "ECIESCircuit0";
    const RATE: usize = 4;

    fn check_encode_decode(mode: Mode) {
        let circuit = ECIESPoseidonEncryption::<Circuit, RATE>::setup();

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..64).map(|_| u8::rand(&mut test_rng())).collect::<Vec<u8>>();

            let expected = NativeECIES::<EdwardsParameters>::encode_message(&input).unwrap();

            // Convert the message into bits.
            let mut plaintext_bits = Vec::<Boolean<_>>::with_capacity(input.len() * 8 + 1);
            for byte in input.iter() {
                let mut byte = *byte;
                for _ in 0..8 {
                    plaintext_bits.push(Inject::new(mode, byte & 1 == 1));
                    byte >>= 1;
                }
            }

            Circuit::scope(format!("ECIES {mode} {i}"), || {
                let encoded = circuit.encode_message(&plaintext_bits);
                let circ_decoded = circuit.decode_message(&encoded);
                assert_eq!(expected, encoded.eject_value());
                assert_eq!(plaintext_bits.eject_value(), circ_decoded.eject_value());
            });
        }
    }

    fn check_encrypt_decrypt(mode: Mode) {
        let native = NativeECIES::<EdwardsParameters>::setup(MESSAGE);
        let circuit = ECIESPoseidonEncryption::<Circuit, RATE>::setup();

        for i in 0..ITERATIONS {
            // Sample a random input.
            let input = (0..64).map(|_| u8::rand(&mut test_rng())).collect::<Vec<u8>>();
            let encoded = NativeECIES::<EdwardsParameters>::encode_message(&input).unwrap();
            let symmetric_key = <EdwardsAffine as AffineCurve>::BaseField::rand(&mut test_rng());
            let circ_input = encoded.iter().map(|el| Field::new(mode, *el)).collect::<Vec<Field<_>>>();
            let circ_symmetric_key = Field::new(mode, symmetric_key);
            let expected = native.encrypt(&symmetric_key, &encoded);

            Circuit::scope(format!("ECIES {mode} {i}"), || {
                let encrypted = circuit.encrypt(circ_symmetric_key.clone(), &circ_input);
                let decrypted = circuit.decrypt(circ_symmetric_key, &encrypted);
                assert_eq!(expected, encrypted.eject_value());
                assert_eq!(encoded, decrypted.eject_value());
            });
        }
    }

    #[test]
    fn test_encode_decode_constant() {
        check_encode_decode(Mode::Constant);
    }

    #[test]
    fn test_encode_decode_public() {
        check_encode_decode(Mode::Public);
    }

    #[test]
    fn test_encode_decode_private() {
        check_encode_decode(Mode::Private);
    }

    #[test]
    fn test_encrypt_decrypt_constant() {
        check_encrypt_decrypt(Mode::Constant);
    }

    #[test]
    fn test_encrypt_decrypt_public() {
        check_encrypt_decrypt(Mode::Public);
    }

    #[test]
    fn test_encrypt_decrypt_private() {
        check_encrypt_decrypt(Mode::Private);
    }
}
