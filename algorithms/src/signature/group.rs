// // Copyright (C) 2019-2021 Aleo Systems Inc.
// // This file is part of the snarkVM library.
//
// // The snarkVM library is free software: you can redistribute it and/or modify
// // it under the terms of the GNU General Public License as published by
// // the Free Software Foundation, either version 3 of the License, or
// // (at your option) any later version.
//
// // The snarkVM library is distributed in the hope that it will be useful,
// // but WITHOUT ANY WARRANTY; without even the implied warranty of
// // MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// // GNU General Public License for more details.
//
// // You should have received a copy of the GNU General Public License
// // along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.
//
// use crate::{
//     crypto_hash::PoseidonDefaultParametersField,
//     encryption::{GroupEncryption, GroupEncryptionPublicKey},
//     errors::SignatureError,
//     signature::{Schnorr, SchnorrParameters, SchnorrPublicKey, SchnorrSignature},
//     traits::{EncryptionScheme, SignatureScheme},
// };
// use snarkvm_curves::{
//     traits::{AffineCurve, Group},
//     ProjectiveCurve,
// };
// use snarkvm_fields::ToConstraintField;
// use snarkvm_utilities::{serialize::*, to_bytes_le, FromBytes, ToBytes};
//
// use rand::{CryptoRng, Rng};
// use std::hash::Hash;
//
// /// Map the encryption group into the signature group.
// fn into_signature_group<G: ProjectiveCurve + CanonicalSerialize, SG: ProjectiveCurve + CanonicalDeserialize>(
//     projective: G,
// ) -> SG {
//     let mut bytes = vec![];
//     CanonicalSerialize::serialize(&projective.into_affine(), &mut bytes).expect("failed to convert to bytes");
//     CanonicalDeserialize::deserialize(&mut &bytes[..]).expect("failed to convert to signature group")
// }
//
// /// Map the GroupEncryption parameters into a Schnorr signature scheme.
// impl<G: ProjectiveCurve + CanonicalSerialize, SG: ProjectiveCurve + CanonicalDeserialize> From<Vec<G>> for Schnorr<SG> {
//     fn from(parameters: Vec<G>) -> Self {
//         let generator_powers: Vec<SG> = parameters
//             .generator_powers
//             .iter()
//             .map(|p| into_signature_group(*p))
//             .collect();
//
//         let parameters = SchnorrParameters { generator_powers };
//
//         Self { parameters }
//     }
// }
//
// /// Map the GroupEncryption public key into a Schnorr public key.
// impl<G: ProjectiveCurve, SG: ProjectiveCurve + CanonicalSerialize + CanonicalDeserialize>
//     From<GroupEncryptionPublicKey<G>> for SchnorrPublicKey<SG>
// {
//     fn from(public_key: GroupEncryptionPublicKey<G>) -> Self {
//         Self(into_signature_group(public_key.0))
//     }
// }
//
// impl<G: ProjectiveCurve, SG: ProjectiveCurve + Hash + CanonicalSerialize + CanonicalDeserialize> SignatureScheme
//     for GroupEncryption<G, SG>
// where
//     <SG::Affine as AffineCurve>::BaseField: PoseidonDefaultParametersField,
//     SG: ToConstraintField<<SG::Affine as AffineCurve>::BaseField>,
// {
//     type Parameters = Vec<G>;
//     type PrivateKey = <G as Group>::ScalarField;
//     type PublicKey = GroupEncryptionPublicKey<G>;
//     type RandomizedPrivateKey = <G as Group>::ScalarField;
//     type Randomizer = <G as Group>::ScalarField;
//     type Signature = SchnorrSignature<SG>;
//
//     fn setup<R: Rng + CryptoRng>(rng: &mut R) -> Result<Self, SignatureError> {
//         Ok(<Self as EncryptionScheme>::setup(rng))
//     }
//
//     fn parameters(&self) -> &Self::Parameters {
//         &self.parameters
//     }
//
//     fn generate_private_key<R: Rng + CryptoRng>(&self, rng: &mut R) -> Result<Self::PrivateKey, SignatureError> {
//         Ok(<Self as EncryptionScheme>::generate_private_key(self, rng))
//     }
//
//     fn generate_public_key(&self, private_key: &Self::PrivateKey) -> Result<Self::PublicKey, SignatureError> {
//         Ok(<Self as EncryptionScheme>::generate_public_key(self, private_key).unwrap())
//     }
//
//     fn randomize_private_key(
//         &self,
//         _private_key: &Self::PrivateKey,
//         _randomizer: &Self::Randomizer,
//     ) -> Result<Self::RandomizedPrivateKey, SignatureError> {
//         unimplemented!()
//     }
//
//     fn randomize_public_key(
//         &self,
//         _public_key: &Self::PublicKey,
//         _randomizer: &Self::Randomizer,
//     ) -> Result<Self::PublicKey, SignatureError> {
//         unimplemented!()
//     }
//
//     fn sign<R: Rng + CryptoRng>(
//         &self,
//         private_key: &Self::PrivateKey,
//         message: &[u8],
//         rng: &mut R,
//     ) -> Result<Self::Signature, SignatureError> {
//         let schnorr_signature: Schnorr<SG> = self.parameters.clone().into();
//         let private_key = <SG as Group>::ScalarField::read_le(&to_bytes_le![private_key]?[..])?;
//
//         Ok(schnorr_signature.sign(&private_key, message, rng)?)
//     }
//
//     fn sign_randomized<R: Rng + CryptoRng>(
//         &self,
//         _randomized_private_key: &Self::RandomizedPrivateKey,
//         _message: &[u8],
//         _rng: &mut R,
//     ) -> Result<Self::Signature, SignatureError> {
//         unimplemented!()
//     }
//
//     fn verify(
//         &self,
//         public_key: &Self::PublicKey,
//         message: &[u8],
//         signature: &Self::Signature,
//     ) -> Result<bool, SignatureError> {
//         let schnorr_signature: Schnorr<SG> = self.parameters.clone().into();
//         let schnorr_public_key: SchnorrPublicKey<SG> = (*public_key).into();
//
//         Ok(schnorr_signature.verify(&schnorr_public_key, message, signature)?)
//     }
// }
