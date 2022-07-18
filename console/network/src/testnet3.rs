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

lazy_static! {
    /// The group bases for the Aleo signature and encryption schemes.
    pub static ref GENERATOR_G: Vec<Group<Testnet3>> = Testnet3::new_bases("AleoAccountEncryptionAndSignatureScheme0");

    /// The balance commitment domain as a constant field element.
    pub static ref BCM_DOMAIN: Field<Testnet3> = Field::<Testnet3>::new_domain_separator("AleoBalanceCommitment0");
    /// The encryption domain as a constant field element.
    pub static ref ENCRYPTION_DOMAIN: Field<Testnet3> = Field::<Testnet3>::new_domain_separator("AleoSymmetricEncryption0");
    /// The MAC domain as a constant field element.
    pub static ref MAC_DOMAIN: Field<Testnet3> = Field::<Testnet3>::new_domain_separator("AleoSymmetricKeyCommitment0");
    /// The randomizer domain as a constant field element.
    pub static ref RANDOMIZER_DOMAIN: Field<Testnet3> = Field::<Testnet3>::new_domain_separator("AleoRandomizer0");
    /// The balance commitment randomizer domain as a constant field element.
    pub static ref R_BCM_DOMAIN: Field<Testnet3> = Field::<Testnet3>::new_domain_separator("AleoBalanceRandomizer0");
    /// The serial number domain as a constant field element.
    pub static ref SERIAL_NUMBER_DOMAIN: Field<Testnet3> = Field::<Testnet3>::new_domain_separator("AleoSerialNumber0");

    /// The BHP hash function, which can take an input of up to 256 bits.
    pub static ref BHP_256: BHP256<Testnet3> = BHP256::<Testnet3>::setup("AleoBHP256").expect("Failed to setup BHP256");
    /// The BHP hash function, which can take an input of up to 512 bits.
    pub static ref BHP_512: BHP512<Testnet3> = BHP512::<Testnet3>::setup("AleoBHP512").expect("Failed to setup BHP512");
    /// The BHP hash function, which can take an input of up to 768 bits.
    pub static ref BHP_768: BHP768<Testnet3> = BHP768::<Testnet3>::setup("AleoBHP768").expect("Failed to setup BHP768");
    /// The BHP hash function, which can take an input of up to 1024 bits.
    pub static ref BHP_1024: BHP1024<Testnet3> = BHP1024::<Testnet3>::setup("AleoBHP1024").expect("Failed to setup BHP1024");

    /// The Pedersen hash function, which can take an input of up to 64 bits.
    pub static ref PEDERSEN_64: Pedersen64<Testnet3> = Pedersen64::<Testnet3>::setup("AleoPedersen64");
    /// The Pedersen hash function, which can take an input of up to 128 bits.
    pub static ref PEDERSEN_128: Pedersen128<Testnet3> = Pedersen128::<Testnet3>::setup("AleoPedersen128");

    /// The Poseidon hash function, using a rate of 2.
    pub static ref POSEIDON_2: Poseidon2<Testnet3> = Poseidon2::<Testnet3>::setup("AleoPoseidon2").expect("Failed to setup Poseidon2");
    /// The Poseidon hash function, using a rate of 4.
    pub static ref POSEIDON_4: Poseidon4<Testnet3> = Poseidon4::<Testnet3>::setup("AleoPoseidon4").expect("Failed to setup Poseidon4");
    /// The Poseidon hash function, using a rate of 8.
    pub static ref POSEIDON_8: Poseidon8<Testnet3> = Poseidon8::<Testnet3>::setup("AleoPoseidon8").expect("Failed to setup Poseidon8");
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Testnet3;

impl Testnet3 {
    /// Initializes a new instance of group bases from a given input domain message.
    fn new_bases(message: &str) -> Vec<Group<Self>> {
        // Hash the given message to a point on the curve, to initialize the starting base.
        let (base, _, _) = Blake2Xs::hash_to_curve::<<Self as Environment>::Affine>(message);

        // Compute the bases up to the size of the scalar field (in bits).
        let mut g = Group::<Self>::new(base);
        let mut g_bases = Vec::with_capacity(Scalar::<Self>::size_in_bits());
        for _ in 0..Scalar::<Self>::size_in_bits() {
            g_bases.push(g);
            g = g.double();
        }
        g_bases
    }
}

impl Environment for Testnet3 {
    type Affine = <Console as Environment>::Affine;
    type AffineParameters = <Console as Environment>::AffineParameters;
    type BigInteger = <Console as Environment>::BigInteger;
    type Field = <Console as Environment>::Field;
    type PairingCurve = <Console as Environment>::PairingCurve;
    type Projective = <Console as Environment>::Projective;
    type Scalar = <Console as Environment>::Scalar;
}

impl Network for Testnet3 {
    /// The block hash type.
    type BlockHash = AleoID<Field<Self>, { hrp2!("ab") }>;
    /// The state root type.
    type StateRoot = AleoID<Field<Self>, { hrp2!("ar") }>;
    /// The transaction ID type.
    type TransactionID = AleoID<Field<Self>, { hrp2!("at") }>;
    /// The transition ID type.
    type TransitionID = AleoID<Field<Self>, { hrp2!("as") }>;

    /// The network edition.
    const EDITION: u16 = 0;
    /// The network ID.
    const ID: u16 = 3;
    /// The network name.
    const NAME: &'static str = "Aleo Testnet3";

    /// Returns the balance commitment domain as a constant field element.
    fn bcm_domain() -> Field<Self> {
        *BCM_DOMAIN
    }

    /// Returns the encryption domain as a constant field element.
    fn encryption_domain() -> Field<Self> {
        *ENCRYPTION_DOMAIN
    }

    /// Returns the MAC domain as a constant field element.
    fn mac_domain() -> Field<Self> {
        *MAC_DOMAIN
    }

    /// Returns the randomizer domain as a constant field element.
    fn randomizer_domain() -> Field<Self> {
        *RANDOMIZER_DOMAIN
    }

    /// Returns the balance commitment randomizer domain as a constant field element.
    fn r_bcm_domain() -> Field<Self> {
        *R_BCM_DOMAIN
    }

    /// Returns the serial number domain as a constant field element.
    fn serial_number_domain() -> Field<Self> {
        *SERIAL_NUMBER_DOMAIN
    }

    /// Returns the powers of G.
    fn g_powers() -> &'static Vec<Group<Self>> {
        &GENERATOR_G
    }

    /// Returns the scalar multiplication on the group bases.
    fn g_scalar_multiply(scalar: &Scalar<Self>) -> Group<Self> {
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
    fn commit_bhp256(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>> {
        BHP_256.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 512-bits.
    fn commit_bhp512(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>> {
        BHP_512.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 768-bits.
    fn commit_bhp768(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>> {
        BHP_768.commit(input, randomizer)
    }

    /// Returns a BHP commitment with an input hasher of 1024-bits.
    fn commit_bhp1024(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>> {
        BHP_1024.commit(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    fn commit_ped64(input: &[bool], randomizer: &Scalar<Self>) -> Result<Group<Self>> {
        PEDERSEN_64.commit_uncompressed(input, randomizer)
    }

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    fn commit_ped128(input: &[bool], randomizer: &Scalar<Self>) -> Result<Group<Self>> {
        PEDERSEN_128.commit_uncompressed(input, randomizer)
    }

    /// Returns the BHP hash with an input hasher of 256-bits.
    fn hash_bhp256(input: &[bool]) -> Result<Field<Self>> {
        BHP_256.hash(input)
    }

    /// Returns the BHP hash with an input hasher of 512-bits.
    fn hash_bhp512(input: &[bool]) -> Result<Field<Self>> {
        BHP_512.hash(input)
    }

    /// Returns the BHP hash with an input hasher of 768-bits.
    fn hash_bhp768(input: &[bool]) -> Result<Field<Self>> {
        BHP_768.hash(input)
    }

    /// Returns the BHP hash with an input hasher of 1024-bits.
    fn hash_bhp1024(input: &[bool]) -> Result<Field<Self>> {
        BHP_1024.hash(input)
    }

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    fn hash_ped64(input: &[bool]) -> Result<Field<Self>> {
        PEDERSEN_64.hash(input)
    }

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    fn hash_ped128(input: &[bool]) -> Result<Field<Self>> {
        PEDERSEN_128.hash(input)
    }

    /// Returns the Poseidon hash with an input rate of 2.
    fn hash_psd2(input: &[Field<Self>]) -> Result<Field<Self>> {
        POSEIDON_2.hash(input)
    }

    /// Returns the Poseidon hash with an input rate of 4.
    fn hash_psd4(input: &[Field<Self>]) -> Result<Field<Self>> {
        POSEIDON_4.hash(input)
    }

    /// Returns the Poseidon hash with an input rate of 8.
    fn hash_psd8(input: &[Field<Self>]) -> Result<Field<Self>> {
        POSEIDON_8.hash(input)
    }

    /// Returns the extended Poseidon hash with an input rate of 2.
    fn hash_many_psd2(input: &[Field<Self>], num_outputs: u16) -> Vec<Field<Self>> {
        POSEIDON_2.hash_many(input, num_outputs)
    }

    /// Returns the extended Poseidon hash with an input rate of 4.
    fn hash_many_psd4(input: &[Field<Self>], num_outputs: u16) -> Vec<Field<Self>> {
        POSEIDON_4.hash_many(input, num_outputs)
    }

    /// Returns the extended Poseidon hash with an input rate of 8.
    fn hash_many_psd8(input: &[Field<Self>], num_outputs: u16) -> Vec<Field<Self>> {
        POSEIDON_8.hash_many(input, num_outputs)
    }

    /// Returns the Poseidon hash with an input rate of 2 on the affine curve.
    fn hash_to_group_psd2(input: &[Field<Self>]) -> Result<Group<Self>> {
        POSEIDON_2.hash_to_group(input)
    }

    /// Returns the Poseidon hash with an input rate of 4 on the affine curve.
    fn hash_to_group_psd4(input: &[Field<Self>]) -> Result<Group<Self>> {
        POSEIDON_4.hash_to_group(input)
    }

    /// Returns the Poseidon hash with an input rate of 8 on the affine curve.
    fn hash_to_group_psd8(input: &[Field<Self>]) -> Result<Group<Self>> {
        POSEIDON_8.hash_to_group(input)
    }

    /// Returns the Poseidon hash with an input rate of 2 on the scalar field.
    fn hash_to_scalar_psd2(input: &[Field<Self>]) -> Result<Scalar<Self>> {
        POSEIDON_2.hash_to_scalar(input)
    }

    /// Returns the Poseidon hash with an input rate of 4 on the scalar field.
    fn hash_to_scalar_psd4(input: &[Field<Self>]) -> Result<Scalar<Self>> {
        POSEIDON_4.hash_to_scalar(input)
    }

    /// Returns the Poseidon hash with an input rate of 8 on the scalar field.
    fn hash_to_scalar_psd8(input: &[Field<Self>]) -> Result<Scalar<Self>> {
        POSEIDON_8.hash_to_scalar(input)
    }

    /// Returns a Merkle tree with a BHP leaf hasher of 1024-bits and a BHP path hasher of 512-bits.
    fn merkle_tree_bhp<const DEPTH: u8>(leaves: &[Vec<bool>]) -> Result<BHPMerkleTree<Self, DEPTH>> {
        MerkleTree::new(&*BHP_1024, &*BHP_512, leaves)
    }

    /// Returns a Merkle tree with a Poseidon leaf hasher with input rate of 4 and a Poseidon path hasher with input rate of 2.
    fn merkle_tree_psd<const DEPTH: u8>(leaves: &[Vec<Field<Self>>]) -> Result<PoseidonMerkleTree<Self, DEPTH>> {
        MerkleTree::new(&*POSEIDON_4, &*POSEIDON_2, leaves)
    }

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    fn verify_merkle_path_bhp<const DEPTH: u8>(
        path: &MerklePath<Self, DEPTH>,
        root: &Field<Self>,
        leaf: &Vec<bool>,
    ) -> bool {
        path.verify(&*BHP_1024, &*BHP_512, root, leaf)
    }

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    fn verify_merkle_path_psd<const DEPTH: u8>(
        path: &MerklePath<Self, DEPTH>,
        root: &Field<Self>,
        leaf: &Vec<Field<Self>>,
    ) -> bool {
        path.verify(&*POSEIDON_4, &*POSEIDON_2, root, leaf)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_g_scalar_multiply() {
        // Compute G^r.
        let scalar = Scalar::rand(&mut test_rng());
        let group = CurrentNetwork::g_scalar_multiply(&scalar);
        assert_eq!(group, CurrentNetwork::g_powers()[0] * scalar);
    }
}
