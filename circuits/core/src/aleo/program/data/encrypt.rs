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

impl<A: Aleo, D: DataType<A>> Data<A, D> {
    /// Encrypts `self` under the given Aleo address and randomizer,
    /// turning `self` into `Data::Ciphertext(..)` if the `mode` is private.
    /// Note: The output is guaranteed to satisfy `Data::is_valid(output)`.
    pub fn encrypt(&self, address: Address<A>, randomizer: Scalar<A>) -> Self {
        match self {
            Self::Plaintext(data, Mode::Private) => {
                // Encode the data as field elements.
                let plaintext = Self::encode(data);
                // Compute the data view key.
                let data_view_key = (address.to_group() * randomizer).to_x_coordinate();
                // Prepare a randomizer for each field element.
                let randomizers = A::hash_many_psd8(&[A::encryption_domain(), data_view_key], plaintext.len());
                // Compute the ciphertext field elements.
                let ciphertext = plaintext.iter().zip_eq(randomizers).map(|(p, r)| p + r).collect();
                // Output the ciphertext.
                Self::Ciphertext(ciphertext, Mode::Private)
            }
            _ => (*self).clone(),
        }
    }
}

impl<A: Aleo, D: DataType<A>> Data<A, D> {
    /// Returns a list of field elements encoding the given data.
    pub(super) fn encode(data: &D) -> Vec<Field<A>> {
        // Encode the data as little-endian bits.
        let mut bits = data.to_bits_le();
        // Adds one final bit to the data, to serve as a terminus indicator.
        // During decryption, this final bit ensures we've reached the end.
        bits.push(Boolean::constant(true));
        // Pack the bits into field elements.
        bits.chunks(A::BaseField::size_in_data_bits()).map(Field::from_bits_le).collect()
    }

    /// Returns the recovered data from encoded field elements.
    pub(super) fn decode(plaintext: &[Field<A>]) -> D {
        // Unpack the field elements into bits, and reverse the list to pop the terminus bit off.
        let mut bits =
            plaintext.iter().flat_map(|p| p.to_bits_le()[..A::BaseField::size_in_data_bits()].to_vec()).rev();
        // Remove the terminus bit that was added during encoding.
        for boolean in bits.by_ref() {
            // Drop all extraneous `0` bits, in addition to the final `1` bit.
            if boolean.eject_value() {
                // This case will always be reached, since the terminus bit is always `1`.
                break;
            }
        }
        // Reverse the bits back and recover the data from the bits.
        D::from_bits_le(&bits.rev().collect::<Vec<_>>())
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use snarkvm_algorithms::{encryption::ECIESPoseidonEncryption as NativeECIES, EncryptionScheme};
//     use snarkvm_circuits_environment::Circuit;
//     use snarkvm_curves::{
//         edwards_bls12::{EdwardsAffine, EdwardsParameters},
//         AffineCurve,
//     };
//     use snarkvm_utilities::{test_rng, UniformRand};
//
//     const ITERATIONS: u64 = 10;
//     const MESSAGE: &str = "ECIESCircuit0";
//     const RATE: usize = 4;
//
//     fn check_encode_decode(mode: Mode) {
//         let circuit = ECIESPoseidonEncryption::<Circuit, RATE>::setup();
//
//         for i in 0..ITERATIONS {
//             // Sample a random input.
//             let input = (0..64).map(|_| u8::rand(&mut test_rng())).collect::<Vec<u8>>();
//
//             let expected = NativeECIES::<EdwardsParameters>::encode_message(&input).unwrap();
//
//             // Convert the message into bits.
//             let mut plaintext_bits = Vec::<Boolean<_>>::with_capacity(input.len() * 8 + 1);
//             for byte in input.iter() {
//                 let mut byte = *byte;
//                 for _ in 0..8 {
//                     plaintext_bits.push(Inject::new(mode, byte & 1 == 1));
//                     byte >>= 1;
//                 }
//             }
//
//             Circuit::scope(format!("ECIES {mode} {i}"), || {
//                 let encoded = circuit.encode_message(&plaintext_bits);
//                 let circ_decoded = circuit.decode_message(&encoded);
//                 assert_eq!(expected, encoded.eject_value());
//                 assert_eq!(plaintext_bits.eject_value(), circ_decoded.eject_value());
//             });
//         }
//     }
//
//     fn check_encrypt_decrypt(mode: Mode) {
//         let native = NativeECIES::<EdwardsParameters>::setup(MESSAGE);
//         let circuit = ECIESPoseidonEncryption::<Circuit, RATE>::setup();
//
//         for i in 0..ITERATIONS {
//             // Sample a random input.
//             let input = (0..64).map(|_| u8::rand(&mut test_rng())).collect::<Vec<u8>>();
//             let encoded = NativeECIES::<EdwardsParameters>::encode_message(&input).unwrap();
//             let symmetric_key = <EdwardsAffine as AffineCurve>::BaseField::rand(&mut test_rng());
//             let circ_input = encoded.iter().map(|el| Field::new(mode, *el)).collect::<Vec<Field<_>>>();
//             let circ_symmetric_key = Field::new(mode, symmetric_key);
//             let expected = native.encrypt(&symmetric_key, &encoded);
//
//             Circuit::scope(format!("ECIES {mode} {i}"), || {
//                 let encrypted = circuit.encrypt(circ_symmetric_key.clone(), &circ_input);
//                 let decrypted = circuit.decrypt(circ_symmetric_key, &encrypted);
//                 assert_eq!(expected, encrypted.eject_value());
//                 assert_eq!(encoded, decrypted.eject_value());
//             });
//         }
//     }
//
//     #[test]
//     fn test_encode_decode_constant() {
//         check_encode_decode(Mode::Constant);
//     }
//
//     #[test]
//     fn test_encode_decode_public() {
//         check_encode_decode(Mode::Public);
//     }
//
//     #[test]
//     fn test_encode_decode_private() {
//         check_encode_decode(Mode::Private);
//     }
//
//     #[test]
//     fn test_encrypt_decrypt_constant() {
//         check_encrypt_decrypt(Mode::Constant);
//     }
//
//     #[test]
//     fn test_encrypt_decrypt_public() {
//         check_encrypt_decrypt(Mode::Public);
//     }
//
//     #[test]
//     fn test_encrypt_decrypt_private() {
//         check_encrypt_decrypt(Mode::Private);
//     }
// }
