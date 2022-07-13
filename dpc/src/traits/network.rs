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

use crate::{
    Block,
    Ciphertext,
    InputPublicVariables,
    OutputPublicVariables,
    PoSWScheme,
    ProgramPublicVariables,
    ValueBalanceCommitment,
};
use snarkvm_algorithms::prelude::*;
use snarkvm_curves::{AffineCurve, PairingEngine, ProjectiveCurve, TwistedEdwardsParameters};
use snarkvm_fields::{Field, PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    traits::algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget},
    FpGadget,
    GroupGadget,
    MaskedCRHGadget,
};
use snarkvm_utilities::{
    fmt::{Debug, Display},
    hash::Hash,
    FromBytes,
    ToBytes,
    ToMinimalBits,
    Uniform,
};

use anyhow::Result;
use serde::{de::DeserializeOwned, Serialize};
use std::{borrow::Borrow, ops::Deref, str::FromStr};

pub trait Bech32Locator<F: Field>:
    From<F>
    + Borrow<F>
    + Deref<Target = F>
    + ToConstraintField<F>
    + Into<Vec<F>>
    + Uniform
    + Copy
    + Clone
    + Default
    + Debug
    + Display
    + FromStr
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
    fn size_in_bytes() -> usize;
    fn number_of_data_characters() -> usize;
}

pub trait Bech32Object<T: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send>:
    From<T>
    + Borrow<T>
    + Deref<Target = T>
    + Clone
    + Debug
    + Display
    + ToBytes
    + FromBytes
    + PartialEq
    + Eq
    + Serialize
    + DeserializeOwned
    + Sync
    + Send
{
    fn prefix() -> String;
    fn size_in_bytes() -> usize;
}

#[rustfmt::skip]
pub trait Network: 'static + Copy + Clone + Debug + Default + PartialEq + Eq + Serialize + DeserializeOwned + Send + Sync {
    const NETWORK_ID: u16;
    const NETWORK_NAME: &'static str;

    const NUM_TRANSITIONS: u8;
    const NUM_EVENTS: u16;

    const NUM_INPUTS: u16;
    const NUM_OUTPUTS: u16;

    const BLOCK_HASH_PREFIX: u16;
    const LEDGER_ROOT_PREFIX: u16;
    const PROGRAM_ID_PREFIX: u16;
    const TRANSITION_ID_PREFIX: u16;
    const TRANSACTION_ID_PREFIX: u16;

    const COMMITMENT_PREFIX: u16;
    const FUNCTION_INPUTS_HASH_PREFIX: u16;
    const FUNCTION_ID_PREFIX: u16;
    const HEADER_NONCE_PREFIX: u16;
    const HEADER_ROOT_PREFIX: u16;
    const HEADER_TRANSACTIONS_ROOT_PREFIX: u16;
    const RECORD_RANDOMIZER_PREFIX: u16;
    const RECORD_VIEW_KEY_COMMITMENT_PREFIX: u16;
    const SERIAL_NUMBER_PREFIX: u16;

    const HEADER_PROOF_PREFIX: u32;
    const PROGRAM_PROOF_PREFIX: u32;
    const RECORD_CIPHERTEXT_PREFIX: u32;
    const RECORD_VIEW_KEY_PREFIX: u32;
    const SIGNATURE_PREFIX: u32;
    const VALUE_COMMITMENT_PREFIX: u32;
    const VALUE_BALANCE_COMMITMENT_PREFIX: u32;
    
    /// Split circuit id prefixes.
    const INPUT_CIRCUIT_ID_PREFIX: u16;
    const OUTPUT_CIRCUIT_ID_PREFIX: u16;

    /// Split circuit proof prefixes.
    const INPUT_PROOF_PREFIX: u32;
    const OUTPUT_PROOF_PREFIX: u32;

    const ADDRESS_SIZE_IN_BYTES: usize;
    const HEADER_SIZE_IN_BYTES: usize;
    const HEADER_PROOF_SIZE_IN_BYTES: usize;
    const PROGRAM_PROOF_SIZE_IN_BYTES: usize;
    const PROGRAM_ID_SIZE_IN_BYTES: usize;
    const RECORD_CIPHERTEXT_SIZE_IN_BYTES: usize;
    const RECORD_PAYLOAD_SIZE_IN_BYTES: usize;
    const RECORD_VIEW_KEY_SIZE_IN_BYTES: usize;
    const SIGNATURE_SIZE_IN_BYTES: usize;
    const VALUE_COMMITMENT_SIZE_IN_BYTES: usize;
    const VALUE_BALANCE_COMMITMENT_SIZE_IN_BYTES: usize;

    /// Split circuit proof sizes.
    const INPUT_PROOF_SIZE_IN_BYTES: usize;
    const OUTPUT_PROOF_SIZE_IN_BYTES: usize;

    const HEADER_TRANSACTIONS_TREE_DEPTH: usize;
    const HEADER_TREE_DEPTH: usize;
    const LEDGER_TREE_DEPTH: usize;
    const PROGRAM_TREE_DEPTH: usize;
    const TRANSITION_TREE_DEPTH: usize;
    const TRANSACTION_TREE_DEPTH: usize;

    const ALEO_BLOCK_TIME_IN_SECS: i64;
    const ALEO_STARTING_SUPPLY_IN_CREDITS: i64;

    /// The maximum future block time.
    const ALEO_FUTURE_TIME_LIMIT_IN_SECS: i64;

    /// The maximum number of blocks that a fork can be.
    const ALEO_MAXIMUM_FORK_DEPTH: u32;

    /// Inner curve type declarations.
    type InnerCurve: PairingEngine<Fr = Self::InnerScalarField, Fq = Self::InnerBaseField>;
    type InnerScalarField: PrimeField;
    type InnerBaseField: PrimeField;

    /// Program curve type declarations.
    type ProgramAffineCurve: AffineCurve<BaseField = Self::InnerScalarField, ScalarField = Self::ProgramScalarField> + ToConstraintField<Self::InnerScalarField>;
    type ProgramAffineCurveGadget: GroupGadget<Self::ProgramAffineCurve, Self::InnerScalarField>;
    type ProgramProjectiveCurve: ProjectiveCurve<BaseField = Self::InnerScalarField>;
    type ProgramCurveParameters: TwistedEdwardsParameters;
    type ProgramScalarField: PrimeField;
    
    /// SNARK for record inputs.
    type InputSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::InnerBaseField, VerifierInput = InputPublicVariables<Self>>;
    type InputProof: Bech32Object<<Self::InputSNARK as SNARK>::Proof>;
    
    /// SNARK for record outputs.
    type OutputSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::InnerBaseField, VerifierInput = OutputPublicVariables<Self>>;
    type OutputProof: Bech32Object<<Self::OutputSNARK as SNARK>::Proof>;

    /// SNARK for Aleo program functions.
    type ProgramSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::InnerBaseField, VerifierInput = ProgramPublicVariables<Self>, ProvingKey = Self::ProgramProvingKey, VerifyingKey = Self::ProgramVerifyingKey, UniversalSetupConfig = usize>;
    type ProgramProvingKey: Clone + ToBytes + FromBytes + Send + Sync;
    type ProgramVerifyingKey: ToConstraintField<Self::InnerBaseField> + Clone + PartialEq + Eq + ToBytes + FromBytes + Serialize + DeserializeOwned + ToMinimalBits + Send + Sync;
    type ProgramProof: Bech32Object<<Self::ProgramSNARK as SNARK>::Proof>;

    /// SNARK for PoSW.
    type PoSWSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::InnerBaseField, VerifierInput = Vec<Self::InnerScalarField>, UniversalSetupConfig = usize>;
    type PoSWProof: Bech32Object<<Self::PoSWSNARK as SNARK>::Proof>;
    type PoSW: PoSWScheme<Self>;

    /// Encryption scheme for accounts. Invoked only over `Self::InnerScalarField`.
    type AccountEncryptionScheme: EncryptionScheme<PrivateKey = Self::ProgramScalarField, PublicKey = Self::ProgramAffineCurve, MessageType = Self::InnerScalarField, CiphertextRandomizer = Self::InnerScalarField, SymmetricKeyCommitment = Self::InnerScalarField>;
    type AccountEncryptionGadget: EncryptionGadget<Self::AccountEncryptionScheme, Self::InnerScalarField>;

    /// PRF for deriving the account private key from a seed.
    type AccountSeedPRF: PRF<Input = Vec<Self::ProgramScalarField>, Seed = Self::AccountSeed, Output = Self::ProgramScalarField>;
    type AccountSeed: FromBytes + ToBytes + PartialEq + Eq + Clone + Default + Debug + Uniform;

    /// Signature scheme for transaction authorizations. Invoked only over `Self::InnerScalarField`.
    type AccountSignatureScheme: SignatureScheme<PrivateKey = (Self::ProgramScalarField, Self::ProgramScalarField), PublicKey = Self::ProgramAffineCurve>
        + SignatureSchemeOperations<AffineCurve = Self::ProgramAffineCurve, BaseField = Self::InnerScalarField, ScalarField = Self::ProgramScalarField, Signature = <Self::AccountSignatureScheme as SignatureScheme>::Signature>;
    type AccountSignatureGadget: SignatureGadget<Self::AccountSignatureScheme, Self::InnerScalarField>;
    type AccountSignaturePublicKey: ToConstraintField<Self::InnerScalarField> + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;
    type AccountSignature: Bech32Object<<Self::AccountSignatureScheme as SignatureScheme>::Signature>;

    /// CRH schemes for the block hash. Invoked only over `Self::InnerScalarField`.
    type BlockHashCRH: CRH<Output = Self::InnerScalarField>;
    type BlockHashCRHGadget: CRHGadget<Self::BlockHashCRH, Self::InnerScalarField>;
    type BlockHash: Bech32Locator<<Self::BlockHashCRH as CRH>::Output>;

    /// Masked Merkle scheme for the block header root on Proof of Succinct Work (PoSW). Invoked only over `Self::InnerScalarField`.
    type BlockHeaderRootCRH: CRH<Output = Self::InnerScalarField>;
    type BlockHeaderRootCRHGadget: CRHGadget<Self::BlockHeaderRootCRH, Self::InnerScalarField, OutputGadget=<Self::BlockHeaderRootTwoToOneCRHGadget as CRHGadget<Self::BlockHeaderRootTwoToOneCRH, Self::InnerScalarField>>::OutputGadget>;
    type BlockHeaderRootTwoToOneCRH: CRH<Output = Self::InnerScalarField>;
    type BlockHeaderRootTwoToOneCRHGadget: MaskedCRHGadget<<Self::BlockHeaderRootParameters as MerkleParameters>::TwoToOneCRH, Self::InnerScalarField, OutputGadget = <Self::PoSWMaskPRFGadget as PRFGadget<Self::PoSWMaskPRF, Self::InnerScalarField>>::Seed>;
    type BlockHeaderRootParameters: MaskedMerkleParameters<LeafCRH= Self::BlockHeaderRootCRH, TwoToOneCRH= Self::BlockHeaderRootTwoToOneCRH>;
    type BlockHeaderRoot: Bech32Locator<<Self::BlockHeaderRootCRH as CRH>::Output>;

    /// Commitment scheme for records. Invoked only over `Self::InnerScalarField`.
    type CommitmentScheme: CRH<Output = Self::InnerScalarField>;
    type CommitmentGadget: CRHGadget<Self::CommitmentScheme, Self::InnerScalarField>;
    type Commitment: Bech32Locator<<Self::CommitmentScheme as CRH>::Output>;

    /// CRH for deriving function IDs. Invoked only over `Self::OuterScalarField`.
    type FunctionIDCRH: CRH<Output = Self::InnerBaseField>;
    type FunctionIDCRHGadget: CRHGadget<Self::FunctionIDCRH, Self::InnerBaseField>;
    type FunctionID: Bech32Locator<<Self::FunctionIDCRH as CRH>::Output>;

    /// Crypto hash for deriving the function inputs hash. Invoked only over `Self::InnerScalarField`.
    type FunctionInputsCRH: CRH<Output = Self::InnerScalarField>;
    type FunctionInputsCRHGadget: CRHGadget<Self::FunctionInputsCRH, Self::InnerScalarField>;
    type FunctionInputsHash: Bech32Locator<<Self::FunctionInputsCRH as CRH>::Output>;
    
    /// CRH for hash of the `Self::InputSNARK` verifying keys. Invoked only over `Self::OuterScalarField`.
    type InputCircuitIDCRH: CRH<Output = Self::InnerBaseField>;
    type InputCircuitID: Bech32Locator<<Self::InputCircuitIDCRH as CRH>::Output>;

    /// CRH for hash of the `Self::OutputSNARK` verifying keys. Invoked only over `Self::OuterScalarField`.
    type OutputCircuitIDCRH: CRH<Output = Self::InnerBaseField>;
    type OutputCircuitID: Bech32Locator<<Self::OutputCircuitIDCRH as CRH>::Output>;

    /// Merkle scheme for computing the ledger root. Invoked only over `Self::InnerScalarField`.
    type LedgerRootCRH: CRH<Output = Self::InnerScalarField>;
    type LedgerRootCRHGadget: CRHGadget<Self::LedgerRootCRH, Self::InnerScalarField, OutputGadget=<Self::LedgerRootTwoToOneCRHGadget as CRHGadget<Self::LedgerRootTwoToOneCRH, Self::InnerScalarField>>::OutputGadget>;
    type LedgerRootTwoToOneCRH: CRH<Output = Self::InnerScalarField>;
    type LedgerRootTwoToOneCRHGadget: CRHGadget<Self::LedgerRootTwoToOneCRH, Self::InnerScalarField>;
    type LedgerRootParameters: MerkleParameters<LeafCRH= Self::LedgerRootCRH, TwoToOneCRH= Self::LedgerRootTwoToOneCRH>;
    type LedgerRoot: Bech32Locator<<Self::LedgerRootCRH as CRH>::Output>;

    /// Schemes for PoSW. Invoked only over `Self::InnerScalarField`.
    type PoSWMaskPRF: PRF<Input = Vec<Self::InnerScalarField>, Seed = Self::InnerScalarField, Output = Self::InnerScalarField>;
    type PoSWMaskPRFGadget: PRFGadget<Self::PoSWMaskPRF, Self::InnerScalarField>;
    type PoSWNonce: Bech32Locator<Self::InnerScalarField>;

    /// CRH for deriving program IDs. Invoked only over `Self::OuterScalarField`.
    type ProgramIDCRH: CRH<Output = Self::InnerScalarField>;
    type ProgramIDTwoToOneCRH: CRH<Output = Self::InnerScalarField>;
    type ProgramIDParameters: MerkleParameters<LeafCRH= Self::ProgramIDCRH, TwoToOneCRH= Self::ProgramIDTwoToOneCRH>;
    type ProgramID: Bech32Locator<<Self::ProgramIDCRH as CRH>::Output>;

    /// Encryption scheme for records. Invoked only over `Self::InnerScalarField`.
    type RecordCiphertext: Bech32Object<Ciphertext<Self>> + Hash;
    type RecordRandomizer: Bech32Locator<<Self::AccountEncryptionScheme as EncryptionScheme>::CiphertextRandomizer>;
    type RecordViewKey: Bech32Object<<Self::AccountEncryptionScheme as EncryptionScheme>::SymmetricKey> + Default;
    type RecordViewKeyCommitment: Bech32Locator<<Self::AccountEncryptionScheme as EncryptionScheme>::SymmetricKeyCommitment>;

    /// PRF for computing serial numbers. Invoked only over `Self::InnerScalarField`.
    type SerialNumberPRF: PRF<Input = Vec<<Self::CommitmentScheme as CRH>::Output>, Seed = Self::InnerScalarField, Output = Self::InnerScalarField>;
    type SerialNumberPRFGadget: PRFGadget<
        Self::SerialNumberPRF, 
        Self::InnerScalarField, 
        Seed = FpGadget<Self::InnerScalarField>,
        Input = Vec<<Self::CommitmentGadget as CRHGadget<Self::CommitmentScheme, Self::InnerScalarField>>::OutputGadget>
    >;
    type SerialNumber: Bech32Locator<<Self::SerialNumberPRF as PRF>::Output>;

    /// Merkle scheme for computing the block transactions root. Invoked only over `Self::InnerScalarField`.
    type TransactionsRootCRH: CRH<Output = Self::InnerScalarField>;
    type TransactionsRootCRHGadget: CRHGadget<Self::TransactionsRootCRH, Self::InnerScalarField, OutputGadget=<Self::TransactionsRootTwoToOneCRHGadget as CRHGadget<Self::TransactionsRootTwoToOneCRH, Self::InnerScalarField>>::OutputGadget>;
    type TransactionsRootTwoToOneCRH: CRH<Output = Self::InnerScalarField>;
    type TransactionsRootTwoToOneCRHGadget: CRHGadget<Self::TransactionsRootTwoToOneCRH, Self::InnerScalarField>;
    type TransactionsRootParameters: MerkleParameters<LeafCRH= Self::TransactionsRootCRH, TwoToOneCRH= Self::TransactionsRootTwoToOneCRH>;
    type TransactionsRoot: Bech32Locator<<Self::TransactionsRootCRH as CRH>::Output>;

    /// Merkle scheme for computing the transaction ID. Invoked only over `Self::InnerScalarField`.
    type TransactionIDCRH: CRH<Output = Self::InnerScalarField>;
    type TransactionIDCRHGadget: CRHGadget<Self::TransactionIDCRH, Self::InnerScalarField, OutputGadget=<Self::TransactionIDTwoToOneCRHGadget as CRHGadget<Self::TransactionIDTwoToOneCRH, Self::InnerScalarField>>::OutputGadget>;
    type TransactionIDTwoToOneCRH: CRH<Output = Self::InnerScalarField>;
    type TransactionIDTwoToOneCRHGadget: CRHGadget<Self::TransactionIDTwoToOneCRH, Self::InnerScalarField>;
    type TransactionIDParameters: MerkleParameters<LeafCRH= Self::TransactionIDCRH, TwoToOneCRH= Self::TransactionIDTwoToOneCRH>;
    type TransactionID: Bech32Locator<<Self::TransactionIDCRH as CRH>::Output>;

    /// Merkle scheme for computing the transition ID. Invoked only over `Self::InnerScalarField`.
    type TransitionIDCRH: CRH<Output = Self::InnerScalarField>;
    type TransitionIDCRHGadget: CRHGadget<Self::TransitionIDCRH, Self::InnerScalarField, OutputGadget=<Self::TransitionIDTwoToOneCRHGadget as CRHGadget<Self::TransitionIDTwoToOneCRH, Self::InnerScalarField>>::OutputGadget>;
    type TransitionIDTwoToOneCRH: CRH<Output = Self::InnerScalarField>;
    type TransitionIDTwoToOneCRHGadget: CRHGadget<Self::TransitionIDTwoToOneCRH, Self::InnerScalarField>;
    type TransitionIDParameters: MerkleParameters<LeafCRH= Self::TransitionIDCRH, TwoToOneCRH= Self::TransitionIDTwoToOneCRH>;
    type TransitionID: Bech32Locator<<Self::TransitionIDCRH as CRH>::Output>;

    /// Commitment scheme for value commitments. Invoked only over `Self::InnerScalarField`.
    type ValueCommitmentScheme: CommitmentScheme<Randomness = Self::ProgramScalarField, Output = Self::ProgramAffineCurve>;
    type ValueCommitmentGadget: CommitmentGadget<Self::ValueCommitmentScheme, Self::InnerScalarField, OutputGadget = Self::ProgramAffineCurveGadget>;
    type ValueCommitment: Bech32Object<Self::ProgramAffineCurve>;
    type ValueBalanceCommitment: Bech32Object<ValueBalanceCommitment<Self>>;

    fn account_encryption_scheme() -> &'static Self::AccountEncryptionScheme;
    fn account_signature_scheme() -> &'static Self::AccountSignatureScheme;
    fn block_hash_crh() -> &'static Self::BlockHashCRH;
    fn block_header_root_parameters() -> &'static Self::BlockHeaderRootParameters;
    fn commitment_scheme() -> &'static Self::CommitmentScheme;
    fn function_id_crh() -> &'static Self::FunctionIDCRH;
    fn ledger_root_parameters() -> &'static Self::LedgerRootParameters;
    fn program_id_parameters() -> &'static Self::ProgramIDParameters;
    fn transactions_root_parameters() -> &'static Self::TransactionsRootParameters;
    fn transaction_id_parameters() -> &'static Self::TransactionIDParameters;
    fn transition_id_parameters() -> &'static Self::TransitionIDParameters;
    fn value_commitment_scheme() -> &'static Self::ValueCommitmentScheme;

    fn input_circuit_id_crh() -> &'static Self::InputCircuitIDCRH;
    fn output_circuit_id_crh() -> &'static Self::OutputCircuitIDCRH;

    fn input_circuit_id() -> &'static Self::InputCircuitID;
    fn input_proving_key() -> &'static <Self::InputSNARK as SNARK>::ProvingKey;
    fn input_verifying_key() -> &'static <Self::InputSNARK as SNARK>::VerifyingKey;

    fn output_circuit_id() -> &'static Self::OutputCircuitID;
    fn output_proving_key() -> &'static <Self::OutputSNARK as SNARK>::ProvingKey;
    fn output_verifying_key() -> &'static <Self::OutputSNARK as SNARK>::VerifyingKey;
    
    fn posw_proving_key() -> &'static <Self::PoSWSNARK as SNARK>::ProvingKey;
    fn posw_verifying_key() -> &'static <Self::PoSWSNARK as SNARK>::VerifyingKey;
    fn posw() -> &'static Self::PoSW;

    fn genesis_block() -> &'static Block<Self>;

    /// Returns the function ID given a program function verifying key.
    fn function_id(
        verifying_key: &<Self::ProgramSNARK as SNARK>::VerifyingKey,
    ) -> Result<Self::FunctionID> {
        Ok(Self::function_id_crh().hash(&verifying_key.to_minimal_bits())?.into())
    }
}
