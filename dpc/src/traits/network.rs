// Copyright (C) 2019-2021 Aleo Systems Inc.
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

use crate::{Block, InnerPublicVariables, OuterPublicVariables, PoSWScheme, Program, ProgramPublicVariables};
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, merkle_tree::MerklePath, prelude::*};
use snarkvm_curves::{AffineCurve, PairingEngine, ProjectiveCurve, TwistedEdwardsParameters};
use snarkvm_fields::{Field, PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    traits::algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget},
    GroupGadget,
    MaskedCRHGadget,
    SNARKVerifierGadget,
};
use snarkvm_utilities::{
    fmt::{Debug, Display},
    hash::Hash,
    FromBytes,
    ToBytes,
    ToMinimalBits,
    UniformRand,
};

use anyhow::Result;
use rand::{CryptoRng, Rng};
use serde::{de::DeserializeOwned, Serialize};
use std::{borrow::Borrow, cell::RefCell, ops::Deref, rc::Rc};

pub trait Bech32Scheme<F: Field>:
    From<F>
    + Borrow<F>
    + Deref<Target = F>
    + ToConstraintField<F>
    + Into<Vec<F>>
    + UniformRand
    + Copy
    + Clone
    + Default
    + Debug
    + Display
    + ToBytes
    + FromBytes
    + Serialize
    + DeserializeOwned
    + PartialEq
    + Eq
    + Hash
    + Sync
    + Send
{
    fn prefix() -> String;
    fn data_size_in_bytes() -> usize;
    fn data_string_length() -> usize;
}

#[rustfmt::skip]
pub trait Network: 'static + Copy + Clone + Debug + Default + PartialEq + Eq + Serialize + Send + Sync {
    const NETWORK_ID: u16;
    const NETWORK_NAME: &'static str;

    const NUM_INPUT_RECORDS: usize;
    const NUM_OUTPUT_RECORDS: usize;
    const NUM_TOTAL_RECORDS: usize = Self::NUM_INPUT_RECORDS + Self::NUM_OUTPUT_RECORDS;

    const BLOCK_HASH_PREFIX: u16;
    const LEDGER_ROOT_PREFIX: u16;
    const PROGRAM_ID_PREFIX: u16;
    const RECORD_CIPHERTEXT_ID_PREFIX: u16;
    const TRANSITION_ID_PREFIX: u16;
    const TRANSACTION_ID_PREFIX: u16;
    const COMMITMENT_PREFIX: u16;
    const COMMITMENT_RANDOMNESS_PREFIX: u16;
    const FUNCTION_ID_PREFIX: u16;
    const INNER_CIRCUIT_ID_PREFIX: u16;
    const SERIAL_NUMBER_PREFIX: u16;
    const TRANSACTIONS_ROOT_PREFIX: u16;

    const ADDRESS_SIZE_IN_BYTES: usize;
    const CIPHERTEXT_SIZE_IN_BYTES: usize;
    const PAYLOAD_SIZE_IN_BYTES: usize;
    const RECORD_SIZE_IN_BYTES: usize;

    const NUM_TRANSITIONS: u8;
    const NUM_EVENTS: u16;

    const TRANSITION_SIZE_IN_BYTES: usize;
    const TRANSITION_TREE_DEPTH: u32;

    const POSW_PROOF_SIZE_IN_BYTES: usize;
    const POSW_NUM_LEAVES: usize;
    const POSW_TREE_DEPTH: usize;
    
    const ALEO_STARTING_SUPPLY_IN_CREDITS: i64;

    /// Inner curve type declarations.
    type InnerCurve: PairingEngine<Fr = Self::InnerScalarField, Fq = Self::OuterScalarField>;
    type InnerScalarField: PrimeField + PoseidonDefaultParametersField;

    /// Outer curve type declarations.
    type OuterCurve: PairingEngine;
    type OuterBaseField: PrimeField;
    type OuterScalarField: PrimeField;

    /// Program curve type declarations.
    type ProgramAffineCurve: AffineCurve<BaseField = Self::ProgramBaseField>;
    type ProgramAffineCurveGadget: GroupGadget<Self::ProgramAffineCurve, Self::InnerScalarField>;
    type ProgramProjectiveCurve: ProjectiveCurve<BaseField = Self::ProgramBaseField>;
    type ProgramCurveParameters: TwistedEdwardsParameters;
    type ProgramBaseField: PrimeField;
    type ProgramScalarField: PrimeField;

    /// SNARK for inner circuit proof generation.
    type InnerSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::OuterScalarField, VerifierInput = InnerPublicVariables<Self>>;
    type InnerSNARKGadget: SNARKVerifierGadget<Self::InnerSNARK>;

    /// SNARK for proof-verification checks.
    type OuterSNARK: SNARK<ScalarField = Self::OuterScalarField, BaseField = Self::OuterBaseField, VerifierInput = OuterPublicVariables<Self>, Proof = Self::OuterProof>;
    type OuterProof: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Serialize + DeserializeOwned + Sync + Send;

    /// SNARK for Aleo programs.
    type ProgramSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::OuterScalarField, VerifierInput = ProgramPublicVariables<Self>, ProvingKey = Self::ProgramProvingKey, VerifyingKey = Self::ProgramVerifyingKey, Proof = Self::ProgramProof, UniversalSetupConfig = usize>;
    type ProgramSNARKGadget: SNARKVerifierGadget<Self::ProgramSNARK>;
    type ProgramProvingKey: Clone + ToBytes + FromBytes + Send + Sync;
    type ProgramVerifyingKey: ToConstraintField<Self::OuterScalarField> + Clone + ToBytes + FromBytes + ToMinimalBits + Send + Sync;
    type ProgramProof: Clone + Debug + ToBytes + FromBytes + Sync + Send;

    /// SNARK for PoSW.
    type PoSWSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::OuterScalarField, VerifierInput = Vec<Self::InnerScalarField>, Proof = Self::PoSWProof, UniversalSetupConfig = usize>;
    type PoSWProof: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send;
    
    /// Encryption scheme for account records. Invoked only over `Self::InnerScalarField`.
    type AccountEncryptionScheme: EncryptionScheme<PrivateKey = Self::ProgramScalarField, PublicKey = Self::ProgramAffineCurve>;
    type AccountEncryptionGadget: EncryptionGadget<Self::AccountEncryptionScheme, Self::InnerScalarField>;

    /// PRF for deriving the account private key from a seed.
    type AccountSeedPRF: PRF<Input = Vec<Self::ProgramScalarField>, Seed = Self::AccountSeed, Output = Self::ProgramScalarField>;
    type AccountSeed: FromBytes + ToBytes + PartialEq + Eq + Clone + Default + Debug + UniformRand;

    /// Signature scheme for transaction authorizations. Invoked only over `Self::InnerScalarField`.
    type AccountSignatureScheme: SignatureScheme<PrivateKey = (Self::ProgramScalarField, Self::ProgramScalarField), PublicKey = Self::ProgramAffineCurve, Signature = Self::AccountSignature>
        + SignatureSchemeOperations<AffineCurve = Self::ProgramAffineCurve, BaseField = Self::ProgramBaseField, ScalarField = Self::ProgramScalarField, Signature = Self::AccountSignature>;
    type AccountSignatureGadget: SignatureGadget<Self::AccountSignatureScheme, Self::InnerScalarField>;
    type AccountSignaturePublicKey: ToConstraintField<Self::InnerScalarField> + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;
    type AccountSignature: Clone + Debug + Default + ToBytes + FromBytes + Serialize + DeserializeOwned + Send + Sync + PartialEq + Eq;

    /// CRH schemes for the block hash. Invoked only over `Self::InnerScalarField`.
    type BlockHashCRH: CRH<Output = Self::InnerScalarField>;
    type BlockHashCRHGadget: CRHGadget<Self::BlockHashCRH, Self::InnerScalarField>;
    type BlockHash: Bech32Scheme<<Self::BlockHashCRH as CRH>::Output>;

    /// Masked Merkle scheme for the block header root on Proof of Succinct Work (PoSW). Invoked only over `Self::InnerScalarField`.
    type BlockHeaderRootCRH: CRH<Output = Self::BlockHeaderRoot>;
    type BlockHeaderRootCRHGadget: MaskedCRHGadget<<Self::BlockHeaderRootParameters as MerkleParameters>::H, Self::InnerScalarField, OutputGadget = <Self::PoSWMaskPRFGadget as PRFGadget<Self::PoSWMaskPRF, Self::InnerScalarField>>::Seed>;
    type BlockHeaderRootParameters: MaskedMerkleParameters<H = Self::BlockHeaderRootCRH>;
    type BlockHeaderRoot: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// CRH scheme for encrypted record ID. Invoked only over `Self::InnerScalarField`.
    type CiphertextIDCRH: CRH<Output = Self::InnerScalarField>;
    type CiphertextIDCRHGadget: CRHGadget<Self::CiphertextIDCRH, Self::InnerScalarField>;
    type CiphertextID: Bech32Scheme<<Self::CiphertextIDCRH as CRH>::Output>;

    /// Commitment scheme for records. Invoked only over `Self::InnerScalarField`.
    type CommitmentScheme: CommitmentScheme<Randomness = Self::ProgramScalarField, Output = Self::InnerScalarField>;
    type CommitmentGadget: CommitmentGadget<Self::CommitmentScheme, Self::InnerScalarField>;
    type CommitmentRandomness: Bech32Scheme<<Self::CommitmentScheme as CommitmentScheme>::Randomness>;
    type Commitment: Bech32Scheme<<Self::CommitmentScheme as CommitmentScheme>::Output>;

    /// CRH for deriving function IDs. Invoked only over `Self::OuterScalarField`.
    type FunctionIDCRH: CRH<Output = Self::OuterScalarField>;
    type FunctionIDCRHGadget: CRHGadget<Self::FunctionIDCRH, Self::OuterScalarField>;
    type FunctionID: Bech32Scheme<<Self::FunctionIDCRH as CRH>::Output>;

    /// Crypto hash for deriving the function inputs digest. Invoked only over `Self::InnerScalarField`.
    type FunctionInputsCRH: CRH<Output = Self::FunctionInputsDigest>;
    type FunctionInputsCRHGadget: CRHGadget<Self::FunctionInputsCRH, Self::InnerScalarField>;
    type FunctionInputsDigest: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;
    
    /// CRH for hash of the `Self::InnerSNARK` verifying keys. Invoked only over `Self::OuterScalarField`.
    type InnerCircuitIDCRH: CRH<Output = Self::OuterScalarField>;
    type InnerCircuitIDCRHGadget: CRHGadget<Self::InnerCircuitIDCRH, Self::OuterScalarField>;
    type InnerCircuitID: Bech32Scheme<<Self::InnerCircuitIDCRH as CRH>::Output>;

    /// Merkle scheme for computing the ledger root. Invoked only over `Self::InnerScalarField`.
    type LedgerRootCRH: CRH<Output = Self::InnerScalarField>;
    type LedgerRootCRHGadget: CRHGadget<Self::LedgerRootCRH, Self::InnerScalarField>;
    type LedgerRootParameters: MerkleParameters<H = Self::LedgerRootCRH>;
    type LedgerRoot: Bech32Scheme<<Self::LedgerRootCRH as CRH>::Output>;

    /// Schemes for PoSW. Invoked only over `Self::InnerScalarField`.
    type PoSWMaskPRF: PRF<Input = Vec<Self::InnerScalarField>, Seed = Self::BlockHeaderRoot, Output = Self::InnerScalarField>;
    type PoSWMaskPRFGadget: PRFGadget<Self::PoSWMaskPRF, Self::InnerScalarField>;
    type PoSW: PoSWScheme<Self>;
    
    /// CRH for deriving program IDs. Invoked only over `Self::OuterScalarField`.
    type ProgramIDCRH: CRH<Output = Self::OuterScalarField>;
    type ProgramIDCRHGadget: CRHGadget<Self::ProgramIDCRH, Self::OuterScalarField>;
    type ProgramIDParameters: MerkleParameters<H = Self::ProgramIDCRH>;
    type ProgramID: Bech32Scheme<<Self::ProgramIDCRH as CRH>::Output>;

    /// PRF for computing serial numbers. Invoked only over `Self::InnerScalarField`.
    type SerialNumberPRF: PRF<Input = Vec<Self::InnerScalarField>, Seed = Self::InnerScalarField, Output = Self::InnerScalarField>;
    type SerialNumberPRFGadget: PRFGadget<Self::SerialNumberPRF, Self::InnerScalarField>;
    type SerialNumber: Bech32Scheme<<Self::SerialNumberPRF as PRF>::Output>;

    /// Merkle scheme for computing the block transactions root. Invoked only over `Self::InnerScalarField`.
    type TransactionsRootCRH: CRH<Output = Self::InnerScalarField>;
    type TransactionsRootCRHGadget: CRHGadget<Self::TransactionsRootCRH, Self::InnerScalarField>;
    type TransactionsRootParameters: MerkleParameters<H = Self::TransactionsRootCRH>;
    type TransactionsRoot: Bech32Scheme<<Self::TransactionsRootCRH as CRH>::Output>;

    /// Merkle scheme for computing the transaction ID. Invoked only over `Self::InnerScalarField`.
    type TransactionIDCRH: CRH<Output = Self::InnerScalarField>;
    type TransactionIDCRHGadget: CRHGadget<Self::TransactionIDCRH, Self::InnerScalarField>;
    type TransactionIDParameters: MerkleParameters<H = Self::TransactionIDCRH>;
    type TransactionID: Bech32Scheme<<Self::TransactionIDCRH as CRH>::Output>;

    /// Merkle scheme for computing the transition ID. Invoked only over `Self::InnerScalarField`.
    type TransitionIDCRH: CRH<Output = Self::InnerScalarField>;
    type TransitionIDCRHGadget: CRHGadget<Self::TransitionIDCRH, Self::InnerScalarField>;
    type TransitionIDParameters: MerkleParameters<H = Self::TransitionIDCRH>;
    type TransitionID: Bech32Scheme<<Self::TransitionIDCRH as CRH>::Output>;

    fn account_encryption_scheme() -> &'static Self::AccountEncryptionScheme;
    fn account_signature_scheme() -> &'static Self::AccountSignatureScheme;
    fn block_hash_crh() -> &'static Self::BlockHashCRH;
    fn block_header_root_parameters() -> &'static Self::BlockHeaderRootParameters;
    fn ciphertext_id_crh() -> &'static Self::CiphertextIDCRH;
    fn commitment_scheme() -> &'static Self::CommitmentScheme;
    fn function_id_crh() -> &'static Self::FunctionIDCRH;
    fn inner_circuit_id_crh() -> &'static Self::InnerCircuitIDCRH;
    fn ledger_root_parameters() -> &'static Self::LedgerRootParameters;
    fn program_id_parameters() -> &'static Self::ProgramIDParameters;
    fn transactions_root_parameters() -> &'static Self::TransactionsRootParameters;
    fn transaction_id_parameters() -> &'static Self::TransactionIDParameters;
    fn transition_id_parameters() -> &'static Self::TransitionIDParameters;

    fn inner_circuit_id() -> &'static Self::InnerCircuitID;
    fn inner_proving_key() -> &'static <Self::InnerSNARK as SNARK>::ProvingKey;
    fn inner_verifying_key() -> &'static <Self::InnerSNARK as SNARK>::VerifyingKey;

    fn noop_program() -> &'static Program<Self>;
    fn noop_program_id() -> &'static Self::ProgramID;
    fn noop_program_path() -> &'static MerklePath<Self::ProgramIDParameters>;
    fn noop_function_id() -> &'static Self::FunctionID;
    fn noop_circuit_proving_key() -> &'static <Self::ProgramSNARK as SNARK>::ProvingKey;
    fn noop_circuit_verifying_key() -> &'static <Self::ProgramSNARK as SNARK>::VerifyingKey;

    fn outer_proving_key() -> &'static <Self::OuterSNARK as SNARK>::ProvingKey;
    fn outer_verifying_key() -> &'static <Self::OuterSNARK as SNARK>::VerifyingKey;

    fn posw_proving_key() -> &'static <Self::PoSWSNARK as SNARK>::ProvingKey;
    fn posw_verifying_key() -> &'static <Self::PoSWSNARK as SNARK>::VerifyingKey;
    fn posw() -> &'static Self::PoSW;

    fn genesis_block() -> &'static Block<Self>;

    /// Returns the function ID given a program function verifying key.
    fn function_id(
        verifying_key: &<Self::ProgramSNARK as SNARK>::VerifyingKey,
    ) -> Result<Self::FunctionID> {
        Ok(Self::function_id_crh().hash_bits(&verifying_key.to_minimal_bits())?.into())
    }

    /// Returns the program SRS for Aleo applications.
    fn program_srs<R: Rng + CryptoRng>(
        rng: &mut R,
    ) -> Rc<RefCell<SRS<R, <Self::ProgramSNARK as SNARK>::UniversalSetupParameters>>>;
}
