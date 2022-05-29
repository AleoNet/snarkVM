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
use snarkvm_console_algorithms::{
    traits::*,
    Blake2Xs,
    Pedersen128,
    Pedersen64,
    Poseidon2,
    Poseidon4,
    Poseidon8,
    BHP1024,
    BHP256,
    BHP512,
    BHP768,
};
use snarkvm_curves::{edwards_bls12::EdwardsAffine, AffineCurve};
use snarkvm_utilities::ToBits;

use anyhow::{anyhow, bail, Result};
use itertools::Itertools;

lazy_static! {
    /// The group bases for the Aleo signature and encryption schemes.
    pub static ref GENERATOR_G: Vec<<Testnet3 as Network>::Projective> = Testnet3::new_bases("AleoAccountEncryptionAndSignatureScheme0");
    /// The encryption domain as a constant field element.
    pub static ref ENCRYPTION_DOMAIN: <Testnet3 as Network>::Field = PrimeField::from_bytes_le_mod_order(b"AleoSymmetricEncryption0");
    /// The MAC domain as a constant field element.
    pub static ref MAC_DOMAIN: <Testnet3 as Network>::Field = PrimeField::from_bytes_le_mod_order(b"AleoSymmetricKeyCommitment0");
    /// The randomizer domain as a constant field element.
    pub static ref RANDOMIZER_DOMAIN: <Testnet3 as Network>::Field = PrimeField::from_bytes_le_mod_order(b"AleoRandomizer0");

    /// The BHP hash function, which can take an input of up to 256 bits.
    pub static ref BHP_256: BHP256<<Testnet3 as Network>::Affine> = BHP256::<<Testnet3 as Network>::Affine>::setup("AleoBHP256").expect("Failed to setup BHP256");
    /// The BHP hash function, which can take an input of up to 512 bits.
    pub static ref BHP_512: BHP512<<Testnet3 as Network>::Affine> = BHP512::<<Testnet3 as Network>::Affine>::setup("AleoBHP512").expect("Failed to setup BHP512");
    /// The BHP hash function, which can take an input of up to 768 bits.
    pub static ref BHP_768: BHP768<<Testnet3 as Network>::Affine> = BHP768::<<Testnet3 as Network>::Affine>::setup("AleoBHP768").expect("Failed to setup BHP768");
    /// The BHP hash function, which can take an input of up to 1024 bits.
    pub static ref BHP_1024: BHP1024<<Testnet3 as Network>::Affine> = BHP1024::<<Testnet3 as Network>::Affine>::setup("AleoBHP1024").expect("Failed to setup BHP1024");

    /// The Pedersen hash function, which can take an input of up to 64 bits.
    pub static ref PEDERSEN_64: Pedersen64<<Testnet3 as Network>::Affine> = Pedersen64::<<Testnet3 as Network>::Affine>::setup("AleoPedersen64");
    /// The Pedersen hash function, which can take an input of up to 128 bits.
    pub static ref PEDERSEN_128: Pedersen128<<Testnet3 as Network>::Affine> = Pedersen128::<<Testnet3 as Network>::Affine>::setup("AleoPedersen128");

    /// The Poseidon hash function, using a rate of 2.
    pub static ref POSEIDON_2: Poseidon2<<Testnet3 as Network>::Field> = Poseidon2::<<Testnet3 as Network>::Field>::setup("AleoPoseidon2").expect("Failed to setup Poseidon2");
    /// The Poseidon hash function, using a rate of 4.
    pub static ref POSEIDON_4: Poseidon4<<Testnet3 as Network>::Field> = Poseidon4::<<Testnet3 as Network>::Field>::setup("AleoPoseidon4").expect("Failed to setup Poseidon4");
    /// The Poseidon hash function, using a rate of 8.
    pub static ref POSEIDON_8: Poseidon8<<Testnet3 as Network>::Field> = Poseidon8::<<Testnet3 as Network>::Field>::setup("AleoPoseidon8").expect("Failed to setup Poseidon8");

    /// The Poseidon hash function on the **scalar** field, using a rate of 2.
    pub static ref POSEIDON_2S: Poseidon2<<Testnet3 as Network>::Scalar> = Poseidon2::<<Testnet3 as Network>::Scalar>::setup("AleoPoseidon2S").expect("Failed to setup Poseidon2S");
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Testnet3;

impl Testnet3 {
    /// Initializes a new instance of group bases from a given input domain message.
    fn new_bases(message: &str) -> Vec<<Self as Network>::Projective> {
        // Hash the given message to a point on the curve, to initialize the starting base.
        let (base, _, _) = Blake2Xs::hash_to_curve::<<Self as Network>::Affine>(message);

        // Compute the bases up to the size of the scalar field (in bits).
        let mut g = base.to_projective();
        let mut g_bases = Vec::with_capacity(<Self as Network>::Scalar::size_in_bits());
        for _ in 0..<Self as Network>::Scalar::size_in_bits() {
            g_bases.push(g);
            g.double_in_place();
        }

        g_bases
    }
}

impl Network for Testnet3 {
    type Affine = EdwardsAffine;
    type Field = <Self::Affine as AffineCurve>::BaseField;
    type Projective = <Self::Affine as AffineCurve>::Projective;
    type Scalar = <Self::Affine as AffineCurve>::ScalarField;

    /// The maximum number of bits in data (must not exceed u16::MAX).
    const MAX_DATA_SIZE_IN_FIELDS: u32 = (128 * 1024 * 8) / <Self::Field as PrimeField>::Parameters::CAPACITY;
    /// The maximum number of characters allowed in a string.
    const NUM_STRING_BYTES: u32 = u8::MAX as u32;

    /// A helper method to recover the y-coordinate given the x-coordinate for
    /// a twisted Edwards point, returning the affine curve point.
    fn affine_from_x_coordinate(x: Self::Field) -> Result<Self::Affine> {
        if let Some(element) = Self::Affine::from_x_coordinate(x, true) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }
        if let Some(element) = Self::Affine::from_x_coordinate(x, false) {
            if element.is_in_correct_subgroup_assuming_on_curve() {
                return Ok(element);
            }
        }
        bail!("Failed to recover an affine group from an x-coordinate of {x}")
    }

    /// TODO (howardwu): Refactor Fp256 and Fp384 and deprecate this method.
    /// A helper method to recover a field element from **little-endian** bits.
    fn field_from_bits_le(bits: &[bool]) -> Result<Self::Field> {
        use snarkvm_utilities::FromBits;
        Self::Field::from_repr(<Self::Field as PrimeField>::BigInteger::from_bits_le(bits)?)
            .ok_or_else(|| anyhow!("Invalid field element from bits"))
    }

    /// TODO (howardwu): Refactor Fp256 and Fp384 and deprecate this method.
    /// A helper method to recover a field element from **big-endian** bits.
    fn field_from_bits_be(bits: &[bool]) -> Result<Self::Field> {
        let mut bits = bits.to_vec();
        bits.reverse();
        Self::field_from_bits_le(&bits)
    }

    /// TODO (howardwu): Refactor Fp256 and Fp384 and deprecate this method.
    /// A helper method to recover a scalar from **little-endian** bits.
    fn scalar_from_bits_le(bits: &[bool]) -> Result<Self::Scalar> {
        use snarkvm_utilities::FromBits;
        Self::Scalar::from_repr(<Self::Scalar as PrimeField>::BigInteger::from_bits_le(bits)?)
            .ok_or_else(|| anyhow!("Invalid scalar from bits"))
    }

    /// TODO (howardwu): Refactor Fp256 and Fp384 and deprecate this method.
    /// A helper method to recover a scalar from **big-endian** bits.
    fn scalar_from_bits_be(bits: &[bool]) -> Result<Self::Scalar> {
        let mut bits = bits.to_vec();
        bits.reverse();
        Self::scalar_from_bits_le(&bits)
    }

    /// Returns the encryption domain as a constant field element.
    fn encryption_domain() -> Self::Field {
        *ENCRYPTION_DOMAIN
    }

    /// Returns the MAC domain as a constant field element.
    fn mac_domain() -> Self::Field {
        *MAC_DOMAIN
    }

    /// Returns the randomizer domain as a constant field element.
    fn randomizer_domain() -> Self::Field {
        *RANDOMIZER_DOMAIN
    }

    /// Returns the powers of G.
    fn g_powers() -> &'static Vec<Self::Projective> {
        &GENERATOR_G
    }

    /// Returns the scalar multiplication on the group bases.
    fn g_scalar_multiply(scalar: &Self::Scalar) -> Self::Projective {
        GENERATOR_G
            .iter()
            .zip_eq(&scalar.to_bits_le())
            .filter_map(|(base, bit)| match bit {
                true => Some(base),
                false => None,
            })
            .sum()
    }

    /// Returns a BHP commitment with an input hasher of 256-bits.
    fn commit_bhp256(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field> {
        BHP_256.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 512-bits.
    fn commit_bhp512(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field> {
        BHP_512.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 768-bits.
    fn commit_bhp768(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field> {
        BHP_768.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 1024-bits.
    fn commit_bhp1024(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field> {
        BHP_1024.commit(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    fn commit_ped64(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field> {
        PEDERSEN_64.commit(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    fn commit_ped128(input: &[bool], randomizer: &Self::Scalar) -> Result<Self::Field> {
        PEDERSEN_128.commit(input, randomizer)
    }

    /// Returns the BHP hash with an input hasher of 256-bits.
    fn hash_bhp256(input: &[bool]) -> Result<Self::Field> {
        BHP_256.hash(input)
    }

    /// Returns the BHP hash with an input hasher of 512-bits.
    fn hash_bhp512(input: &[bool]) -> Result<Self::Field> {
        BHP_512.hash(input)
    }

    /// Returns the BHP hash with an input hasher of 768-bits.
    fn hash_bhp768(input: &[bool]) -> Result<Self::Field> {
        BHP_768.hash(input)
    }

    /// Returns the BHP hash with an input hasher of 1024-bits.
    fn hash_bhp1024(input: &[bool]) -> Result<Self::Field> {
        BHP_1024.hash(input)
    }

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    fn hash_ped64(input: &[bool]) -> Result<Self::Field> {
        PEDERSEN_64.hash(input)
    }

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    fn hash_ped128(input: &[bool]) -> Result<Self::Field> {
        PEDERSEN_128.hash(input)
    }

    /// Returns the Poseidon hash with an input rate of 2.
    fn hash_psd2(input: &[Self::Field]) -> Result<Self::Field> {
        POSEIDON_2.hash(input)
    }

    /// Returns the Poseidon hash with an input rate of 4.
    fn hash_psd4(input: &[Self::Field]) -> Result<Self::Field> {
        POSEIDON_4.hash(input)
    }

    /// Returns the Poseidon hash with an input rate of 8.
    fn hash_psd8(input: &[Self::Field]) -> Result<Self::Field> {
        POSEIDON_8.hash(input)
    }

    /// Returns the extended Poseidon hash with an input rate of 2.
    fn hash_many_psd2(input: &[Self::Field], num_outputs: u16) -> Vec<Self::Field> {
        POSEIDON_2.hash_many(input, num_outputs)
    }

    /// Returns the extended Poseidon hash with an input rate of 4.
    fn hash_many_psd4(input: &[Self::Field], num_outputs: u16) -> Vec<Self::Field> {
        POSEIDON_4.hash_many(input, num_outputs)
    }

    /// Returns the extended Poseidon hash with an input rate of 8.
    fn hash_many_psd8(input: &[Self::Field], num_outputs: u16) -> Vec<Self::Field> {
        POSEIDON_8.hash_many(input, num_outputs)
    }

    /// Returns the Poseidon hash with an input rate of 2 on the scalar field.
    fn hash_to_scalar_psd2(input: &[Self::Field]) -> Result<Self::Scalar> {
        POSEIDON_2.hash_to_scalar::<Self::Scalar>(input)
    }

    /// Returns the Poseidon hash with an input rate of 4 on the scalar field.
    fn hash_to_scalar_psd4(input: &[Self::Field]) -> Result<Self::Scalar> {
        POSEIDON_4.hash_to_scalar::<Self::Scalar>(input)
    }

    /// Returns the Poseidon hash with an input rate of 8 on the scalar field.
    fn hash_to_scalar_psd8(input: &[Self::Field]) -> Result<Self::Scalar> {
        POSEIDON_8.hash_to_scalar::<Self::Scalar>(input)
    }

    /// Returns a Merkle tree with a BHP leaf hasher of 1024-bits and a BHP path hasher of 512-bits.
    fn merkle_tree_bhp<const DEPTH: u8>(leaves: &[Vec<bool>]) -> Result<MerkleTree<Self::Field, DEPTH>> {
        MerkleTree::new(&*BHP_1024, &*BHP_512, leaves)
    }

    /// Returns a Merkle tree with a Poseidon leaf hasher with input rate of 4 and a Poseidon path hasher with input rate of 2.
    fn merkle_tree_psd<const DEPTH: u8>(leaves: &[Vec<Self::Field>]) -> Result<MerkleTree<Self::Field, DEPTH>> {
        MerkleTree::new(&*POSEIDON_4, &*POSEIDON_2, leaves)
    }

    /// Returns the Poseidon PRF with an input rate of 2.
    fn prf_psd2(seed: &Self::Field, input: &[Self::Field]) -> Result<Self::Field> {
        POSEIDON_2.prf(seed, input)
    }

    /// Returns the Poseidon PRF with an input rate of 4.
    fn prf_psd4(seed: &Self::Field, input: &[Self::Field]) -> Result<Self::Field> {
        POSEIDON_4.prf(seed, input)
    }

    /// Returns the Poseidon PRF with an input rate of 8.
    fn prf_psd8(seed: &Self::Field, input: &[Self::Field]) -> Result<Self::Field> {
        POSEIDON_8.prf(seed, input)
    }

    /// Returns the Poseidon PRF on the **scalar** field with an input rate of 2.
    fn prf_psd2s(seed: &Self::Scalar, input: &[Self::Scalar]) -> Result<Self::Scalar> {
        POSEIDON_2S.prf(seed, input)
    }
}
