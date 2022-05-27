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

impl<A: Aleo> Data<A, Plaintext<A>> {
    /// Encrypts `self` under the given Aleo address and randomizer.
    pub fn encrypt(&self, address: &Address<A>, randomizer: &Scalar<A>) -> Data<A, Ciphertext<A>> {
        // Compute the data view key.
        let data_view_key = (address.to_group() * randomizer).to_x_coordinate();
        // Determine the number of randomizers needed to encrypt the data.
        let num_randomizers = self.0.iter().map(|(_, entry)| entry.num_randomizers()).sum();
        // Prepare a randomizer for each field element.
        let randomizers = A::hash_many_psd8(&[A::encryption_domain(), data_view_key], num_randomizers);
        // Encrypt the data.
        let mut index: usize = 0;
        let mut encrypted_data = Vec::with_capacity(self.0.len());
        for (id, entry, num_randomizers) in self.0.iter().map(|(id, entry)| (id, entry, entry.num_randomizers())) {
            // Retrieve the randomizers for this entry.
            let randomizers = &randomizers[index..index + num_randomizers as usize];
            // Encrypt the entry, and add the entry.
            encrypted_data.push((id.clone(), entry.encrypt(randomizers)));
            // Increment the index.
            index += num_randomizers as usize;
        }
        Data(encrypted_data)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::{account::helpers::generate_account, Circuit, Literal};
    use snarkvm_circuits_types::Field;
    use snarkvm_utilities::{test_crypto_rng, UniformRand};

    use anyhow::Result;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_encrypt_and_decrypt() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            // Generate a private key, compute key, view key, and address.
            let (_private_key, _compute_key, view_key, address) = generate_account()?;

            // Initialize a view key and address.
            let view_key = ViewKey::<Circuit>::new(Mode::Private, *view_key);
            let address = Address::<Circuit>::new(Mode::Private, *address);

            let data = Data(vec![(
                Identifier::from_str("a"),
                Entry::Private(Plaintext::from(Literal::Field(Field::new(Mode::Private, UniformRand::rand(rng))))),
            )]);

            let randomizer = Scalar::new(Mode::Private, UniformRand::rand(rng));
            let ciphertext = data.encrypt(&address, &randomizer);

            let nonce = <Circuit as Aleo>::g_scalar_multiply(&randomizer);
            assert_eq!(data.eject(), ciphertext.decrypt(&view_key, &nonce).eject());
        }
        Ok(())
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
