// Copyright (C) 2019-2023 Aleo Systems Inc.
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

#![forbid(unsafe_code)]
#![allow(clippy::too_many_arguments)]
#![warn(clippy::cast_possible_truncation)]

#[macro_use]
extern crate lazy_static;

pub use snarkvm_console_network_environment as environment;
pub use snarkvm_console_network_environment::*;

mod helpers;
pub use helpers::*;

mod testnet3;
pub use testnet3::*;

pub mod prelude {
    pub use crate::{environment::prelude::*, Network};
}

use crate::environment::prelude::*;
use snarkvm_algorithms::{
    crypto_hash::PoseidonSponge,
    snark::marlin::{CircuitProvingKey, CircuitVerifyingKey, MarlinHidingMode},
    AlgebraicSponge,
};
use snarkvm_console_algorithms::{Poseidon2, Poseidon4, BHP1024, BHP512};
use snarkvm_console_collections::merkle_tree::{MerklePath, MerkleTree};
use snarkvm_console_types::{Field, Group, Scalar};
use snarkvm_curves::PairingEngine;

use indexmap::IndexMap;
use once_cell::sync::OnceCell;
use std::sync::Arc;

/// A helper type for the BHP Merkle tree.
pub type BHPMerkleTree<N, const DEPTH: u8> = MerkleTree<N, BHP1024<N>, BHP512<N>, DEPTH>;
/// A helper type for the Poseidon Merkle tree.
pub type PoseidonMerkleTree<N, const DEPTH: u8> = MerkleTree<N, Poseidon4<N>, Poseidon2<N>, DEPTH>;

/// Helper types for the Marlin parameters.
type Fq<N> = <<N as Environment>::PairingCurve as PairingEngine>::Fq;
pub type FiatShamir<N> = PoseidonSponge<Fq<N>, 2, 1>;
pub type FiatShamirParameters<N> = <FiatShamir<N> as AlgebraicSponge<Fq<N>, 2>>::Parameters;

/// Helper types for the Marlin proving and verifying key.
pub(crate) type MarlinProvingKey<N> = CircuitProvingKey<<N as Environment>::PairingCurve, MarlinHidingMode>;
pub(crate) type MarlinVerifyingKey<N> = CircuitVerifyingKey<<N as Environment>::PairingCurve, MarlinHidingMode>;

pub trait Network:
    'static
    + Environment
    + Copy
    + Clone
    + Debug
    + Eq
    + PartialEq
    + core::hash::Hash
    + Serialize
    + DeserializeOwned
    + for<'a> Deserialize<'a>
    + Send
    + Sync
{
    /// The network ID.
    const ID: u16;
    /// The network name.
    const NAME: &'static str;
    /// The network edition.
    const EDITION: u16;

    /// The function name for the inclusion circuit.
    const INCLUSION_FUNCTION_NAME: &'static str;

    /// The fixed timestamp of the genesis block.
    const GENESIS_TIMESTAMP: i64 = 1680307200; // 2023-04-01 00:00:00 UTC
    /// The genesis block coinbase target.
    const GENESIS_COINBASE_TARGET: u64 = (1u64 << 12).saturating_sub(1); // 1111 1111 1111
    /// The genesis block proof target.
    const GENESIS_PROOF_TARGET: u64 = 32; // 0000 0010 0000

    /// The starting supply of Aleo credits.
    const STARTING_SUPPLY: u64 = 1_500_000_000_000_000; // 1.5B credits
    /// The cost in microcredits per byte for the deployment transaction.
    const DEPLOYMENT_FEE_MULTIPLIER: u64 = 1_000; // 1 millicredit per byte

    /// The anchor time per block in seconds, which must be greater than the round time per block.
    const ANCHOR_TIME: u16 = 25;
    /// The coinbase puzzle degree.
    const COINBASE_PUZZLE_DEGREE: u32 = (1 << 13) - 1; // 8,191
    /// The maximum number of prover solutions that can be included per block.
    const MAX_PROVER_SOLUTIONS: usize = 1 << 8; // 256 prover solutions
    /// The number of blocks per epoch (1 hour).
    const NUM_BLOCKS_PER_EPOCH: u32 = 1 << 8; // 256 blocks == ~1 hour

    /// The maximum number of entries in data.
    const MAX_DATA_ENTRIES: usize = 32;
    /// The maximum recursive depth of an entry.
    /// Note: This value must be strictly less than u8::MAX.
    const MAX_DATA_DEPTH: usize = 32;
    /// The maximum number of fields in data (must not exceed u16::MAX).
    #[allow(clippy::cast_possible_truncation)]
    const MAX_DATA_SIZE_IN_FIELDS: u32 = ((128 * 1024 * 8) / Field::<Self>::SIZE_IN_DATA_BITS) as u32;

    /// The minimum number of entries in a struct.
    const MIN_STRUCT_ENTRIES: usize = 1; // This ensures the struct is not empty.
    /// The maximum number of entries in a struct.
    const MAX_STRUCT_ENTRIES: usize = Self::MAX_DATA_ENTRIES;

    /// The minimum number of entries in a record.
    const MIN_RECORD_ENTRIES: usize = 1; // This accounts for 'record.owner'.
    /// The maximum number of entries in a record.
    const MAX_RECORD_ENTRIES: usize = Self::MIN_RECORD_ENTRIES.saturating_add(Self::MAX_DATA_ENTRIES);

    /// The maximum number of mappings in a program.
    const MAX_MAPPINGS: usize = 31;
    /// The maximum number of functions in a program.
    const MAX_FUNCTIONS: usize = 31;
    /// The maximum number of operands in an instruction.
    const MAX_OPERANDS: usize = Self::MAX_INPUTS;
    /// The maximum number of instructions in a closure or function.
    const MAX_INSTRUCTIONS: usize = u16::MAX as usize;
    /// The maximum number of commands in finalize.
    const MAX_COMMANDS: usize = u16::MAX as usize;

    /// The maximum number of inputs per transition.
    const MAX_INPUTS: usize = 16;
    /// The maximum number of outputs per transition.
    const MAX_OUTPUTS: usize = 16;

    /// The state root type.
    type StateRoot: Bech32ID<Field<Self>>;
    /// The block hash type.
    type BlockHash: Bech32ID<Field<Self>>;
    /// The transaction ID type.
    type TransactionID: Bech32ID<Field<Self>>;
    /// The transition ID type.
    type TransitionID: Bech32ID<Field<Self>>;

    /// Returns the genesis block bytes.
    fn genesis_bytes() -> &'static [u8];

    /// Returns the proving key for the given function name in `credits.aleo`.
    fn get_credits_proving_key(function_name: String) -> Result<&'static Arc<MarlinProvingKey<Self>>>;

    /// Returns the verifying key for the given function name in `credits.aleo`.
    fn get_credits_verifying_key(function_name: String) -> Result<&'static Arc<MarlinVerifyingKey<Self>>>;

    /// Returns the `proving key` for the inclusion circuit.
    fn inclusion_proving_key() -> &'static Arc<MarlinProvingKey<Self>>;

    /// Returns the `verifying key` for the inclusion circuit.
    fn inclusion_verifying_key() -> &'static Arc<MarlinVerifyingKey<Self>>;

    /// Returns the powers of `G`.
    fn g_powers() -> &'static Vec<Group<Self>>;

    /// Returns the scalar multiplication on the generator `G`.
    fn g_scalar_multiply(scalar: &Scalar<Self>) -> Group<Self>;

    /// Returns the sponge parameters for Marlin.
    fn marlin_fs_parameters() -> &'static FiatShamirParameters<Self>;

    /// Returns the balance commitment domain as a constant field element.
    fn bcm_domain() -> Field<Self>;

    /// Returns the encryption domain as a constant field element.
    fn encryption_domain() -> Field<Self>;

    /// Returns the graph key domain as a constant field element.
    fn graph_key_domain() -> Field<Self>;

    /// Returns the randomizer domain as a constant field element.
    fn randomizer_domain() -> Field<Self>;

    /// Returns the balance commitment randomizer domain as a constant field element.
    fn r_bcm_domain() -> Field<Self>;

    /// Returns the serial number domain as a constant field element.
    fn serial_number_domain() -> Field<Self>;

    /// Returns a BHP commitment with an input hasher of 256-bits.
    fn commit_bhp256(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>>;

    /// Returns a BHP commitment with an input hasher of 512-bits.
    fn commit_bhp512(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>>;

    /// Returns a BHP commitment with an input hasher of 768-bits.
    fn commit_bhp768(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>>;

    /// Returns a BHP commitment with an input hasher of 1024-bits.
    fn commit_bhp1024(input: &[bool], randomizer: &Scalar<Self>) -> Result<Field<Self>>;

    /// Returns a Pedersen commitment for the given (up to) 64-bit input and randomizer.
    fn commit_ped64(input: &[bool], randomizer: &Scalar<Self>) -> Result<Group<Self>>;

    /// Returns a Pedersen commitment for the given (up to) 128-bit input and randomizer.
    fn commit_ped128(input: &[bool], randomizer: &Scalar<Self>) -> Result<Group<Self>>;

    /// Returns the BHP hash with an input hasher of 256-bits.
    fn hash_bhp256(input: &[bool]) -> Result<Field<Self>>;

    /// Returns the BHP hash with an input hasher of 512-bits.
    fn hash_bhp512(input: &[bool]) -> Result<Field<Self>>;

    /// Returns the BHP hash with an input hasher of 768-bits.
    fn hash_bhp768(input: &[bool]) -> Result<Field<Self>>;

    /// Returns the BHP hash with an input hasher of 1024-bits.
    fn hash_bhp1024(input: &[bool]) -> Result<Field<Self>>;

    /// Returns the Pedersen hash for a given (up to) 64-bit input.
    fn hash_ped64(input: &[bool]) -> Result<Field<Self>>;

    /// Returns the Pedersen hash for a given (up to) 128-bit input.
    fn hash_ped128(input: &[bool]) -> Result<Field<Self>>;

    /// Returns the Poseidon hash with an input rate of 2.
    fn hash_psd2(input: &[Field<Self>]) -> Result<Field<Self>>;

    /// Returns the Poseidon hash with an input rate of 4.
    fn hash_psd4(input: &[Field<Self>]) -> Result<Field<Self>>;

    /// Returns the Poseidon hash with an input rate of 8.
    fn hash_psd8(input: &[Field<Self>]) -> Result<Field<Self>>;

    /// Returns the extended Poseidon hash with an input rate of 2.
    fn hash_many_psd2(input: &[Field<Self>], num_outputs: u16) -> Vec<Field<Self>>;

    /// Returns the extended Poseidon hash with an input rate of 4.
    fn hash_many_psd4(input: &[Field<Self>], num_outputs: u16) -> Vec<Field<Self>>;

    /// Returns the extended Poseidon hash with an input rate of 8.
    fn hash_many_psd8(input: &[Field<Self>], num_outputs: u16) -> Vec<Field<Self>>;

    /// Returns the Poseidon hash with an input rate of 2 on the affine curve.
    fn hash_to_group_psd2(input: &[Field<Self>]) -> Result<Group<Self>>;

    /// Returns the Poseidon hash with an input rate of 4 on the affine curve.
    fn hash_to_group_psd4(input: &[Field<Self>]) -> Result<Group<Self>>;

    /// Returns the Poseidon hash with an input rate of 8 on the affine curve.
    fn hash_to_group_psd8(input: &[Field<Self>]) -> Result<Group<Self>>;

    /// Returns the Poseidon hash with an input rate of 2 on the scalar field.
    fn hash_to_scalar_psd2(input: &[Field<Self>]) -> Result<Scalar<Self>>;

    /// Returns the Poseidon hash with an input rate of 4 on the scalar field.
    fn hash_to_scalar_psd4(input: &[Field<Self>]) -> Result<Scalar<Self>>;

    /// Returns the Poseidon hash with an input rate of 8 on the scalar field.
    fn hash_to_scalar_psd8(input: &[Field<Self>]) -> Result<Scalar<Self>>;

    /// Returns a Merkle tree with a BHP leaf hasher of 1024-bits and a BHP path hasher of 512-bits.
    fn merkle_tree_bhp<const DEPTH: u8>(leaves: &[Vec<bool>]) -> Result<BHPMerkleTree<Self, DEPTH>>;

    /// Returns a Merkle tree with a Poseidon leaf hasher with input rate of 4 and a Poseidon path hasher with input rate of 2.
    fn merkle_tree_psd<const DEPTH: u8>(leaves: &[Vec<Field<Self>>]) -> Result<PoseidonMerkleTree<Self, DEPTH>>;

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    #[allow(clippy::ptr_arg)]
    fn verify_merkle_path_bhp<const DEPTH: u8>(
        path: &MerklePath<Self, DEPTH>,
        root: &Field<Self>,
        leaf: &Vec<bool>,
    ) -> bool;

    /// Returns `true` if the given Merkle path is valid for the given root and leaf.
    #[allow(clippy::ptr_arg)]
    fn verify_merkle_path_psd<const DEPTH: u8>(
        path: &MerklePath<Self, DEPTH>,
        root: &Field<Self>,
        leaf: &Vec<Field<Self>>,
    ) -> bool;
}
