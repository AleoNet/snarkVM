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

impl<N: Network> Data<N, Plaintext<N>> {
    /// Encrypts `self` under the given Aleo address and randomizer.
    pub fn encrypt(&self, address: Address<N>, randomizer: N::Scalar) -> Result<Data<N, Ciphertext<N>>> {
        // Compute the data view key.
        let data_view_key = (*address * randomizer).to_affine().to_x_coordinate();
        // Encrypt the data.
        self.encrypt_symmetric(&data_view_key)
    }

    /// Encrypts `self` under the given data view key.
    pub fn encrypt_symmetric(&self, data_view_key: &N::Field) -> Result<Data<N, Ciphertext<N>>> {
        // Determine the number of randomizers needed to encrypt the data.
        let num_randomizers =
            self.0.iter().map(|(_, entry)| entry.num_randomizers()).collect::<Result<Vec<_>>>()?.iter().sum();
        // Prepare a randomizer for each field element.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), *data_view_key], num_randomizers);
        // Encrypt the data.
        let mut index: usize = 0;
        let mut encrypted_data = Vec::with_capacity(self.0.len());
        for (id, entry, num_randomizers) in self.0.iter().map(|(id, entry)| (id, entry, entry.num_randomizers())) {
            // Retrieve the result for `num_randomizers`.
            let num_randomizers = num_randomizers? as usize;
            // Retrieve the randomizers for this entry.
            let randomizers = &randomizers[index..index + num_randomizers];
            // Encrypt the entry, and add the entry.
            encrypted_data.push((id.clone(), entry.encrypt(randomizers)?));
            // Increment the index.
            index += num_randomizers;
        }
        Ok(Data(encrypted_data))
    }
}

impl<N: Network> Data<N, Ciphertext<N>> {
    /// Decrypts `self` into plaintext using the given view key & nonce.
    pub fn decrypt(&self, view_key: ViewKey<N>, nonce: N::Affine) -> Result<Data<N, Plaintext<N>>> {
        // Compute the data view key.
        let data_view_key = (nonce * *view_key).to_affine().to_x_coordinate();
        // Decrypt the data.
        self.decrypt_symmetric(&data_view_key)
    }

    /// Decrypts `self` into plaintext using the given data view key.
    pub fn decrypt_symmetric(&self, data_view_key: &N::Field) -> Result<Data<N, Plaintext<N>>> {
        // Determine the number of randomizers needed to encrypt the data.
        let num_randomizers =
            self.0.iter().map(|(_, entry)| entry.num_randomizers()).collect::<Result<Vec<_>>>()?.iter().sum();
        // Prepare a randomizer for each field element.
        let randomizers = N::hash_many_psd8(&[N::encryption_domain(), *data_view_key], num_randomizers);
        // Decrypt the data.
        let mut index: usize = 0;
        let mut decrypted_data = Vec::with_capacity(self.0.len());
        for (id, entry, num_randomizers) in self.0.iter().map(|(id, entry)| (id, entry, entry.num_randomizers())) {
            // Retrieve the result for `num_randomizers`.
            let num_randomizers = num_randomizers? as usize;
            // Retrieve the randomizers for this entry.
            let randomizers = &randomizers[index..index + num_randomizers];
            // Decrypt the entry, and add the entry.
            decrypted_data.push((id.clone(), entry.decrypt(randomizers)?));
            // Increment the index.
            index += num_randomizers;
        }
        Ok(Data(decrypted_data))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Literal, PrivateKey, Testnet3};
    use snarkvm_utilities::{test_crypto_rng, UniformRand};

    use core::str::FromStr;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 100;

    #[test]
    fn test_encrypt_and_decrypt() -> Result<()> {
        let rng = &mut test_crypto_rng();

        for _ in 0..ITERATIONS {
            // Sample a view key and address.
            let private_key = PrivateKey::<CurrentNetwork>::new(&mut test_crypto_rng())?;
            let view_key = ViewKey::try_from(&private_key)?;
            let address = Address::try_from(&private_key)?;

            let data = Data(vec![(
                Identifier::from_str("a")?,
                Entry::Private(Plaintext::from(Literal::Field(UniformRand::rand(rng)))),
            )]);

            let randomizer = <CurrentNetwork as Network>::Scalar::rand(rng);
            let ciphertext = data.encrypt(address, randomizer)?;

            let nonce = <CurrentNetwork as Network>::g_scalar_multiply(&randomizer).to_affine();
            assert_eq!(data, ciphertext.decrypt(view_key, nonce)?);
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
