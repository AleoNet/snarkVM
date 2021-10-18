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
use snarkvm_fields::{PrimeField, ToConstraintField};
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
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{cell::RefCell, rc::Rc};

#[rustfmt::skip]
pub trait Network: 'static + Clone + Debug + PartialEq + Eq + Serialize + Send + Sync {
    const NETWORK_ID: u16;
    const NETWORK_NAME: &'static str;

    const NUM_EVENTS: usize;
    const NUM_INPUT_RECORDS: usize;
    const NUM_OUTPUT_RECORDS: usize;
    const NUM_TOTAL_RECORDS: usize = Self::NUM_INPUT_RECORDS + Self::NUM_OUTPUT_RECORDS;

    const ADDRESS_SIZE_IN_BYTES: usize;
    const CIPHERTEXT_SIZE_IN_BYTES: usize;
    const PAYLOAD_SIZE_IN_BYTES: usize;
    const RECORD_SIZE_IN_BYTES: usize;
    const TRANSITION_SIZE_IN_BYTES: usize;
    
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
    type PoswSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::OuterScalarField, VerifierInput = Vec<Self::InnerScalarField>, Proof = Self::PoSWProof, UniversalSetupConfig = usize>;
    type PoSWProof: Clone + Debug + ToBytes + FromBytes + PartialEq + Eq + Sync + Send;
    
    /// Encryption scheme for account records. Invoked only over `Self::InnerScalarField`.
    type AccountEncryptionScheme: EncryptionScheme<PrivateKey = Self::ProgramScalarField, PublicKey = Self::ProgramAffineCurve>;
    type AccountEncryptionGadget: EncryptionGadget<Self::AccountEncryptionScheme, Self::InnerScalarField>;

    /// PRF for deriving the account private key from a seed.
    type AccountPRF: PRF<Input = Vec<Self::ProgramScalarField>, Seed = Self::AccountSeed, Output = Self::ProgramScalarField>;
    type AccountSeed: FromBytes + ToBytes + PartialEq + Eq + Clone + Default + Debug + UniformRand;

    /// Signature scheme for transaction authorizations. Invoked only over `Self::InnerScalarField`.
    type AccountSignatureScheme: SignatureScheme<PrivateKey = (Self::ProgramScalarField, Self::ProgramScalarField), PublicKey = Self::ProgramAffineCurve, Signature = Self::AccountSignature>
        + SignatureSchemeOperations<AffineCurve = Self::ProgramAffineCurve, BaseField = Self::ProgramBaseField, ScalarField = Self::ProgramScalarField, Signature = Self::AccountSignature>;
    type AccountSignatureGadget: SignatureGadget<Self::AccountSignatureScheme, Self::InnerScalarField>;
    type AccountSignaturePublicKey: ToConstraintField<Self::InnerScalarField> + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;
    type AccountSignature: Clone + Debug + Default + ToBytes + FromBytes + Serialize + DeserializeOwned + Send + Sync + PartialEq + Eq;

    /// CRH schemes for the block hash. Invoked only over `Self::InnerScalarField`.
    type BlockHashCRH: CRH<Output = Self::BlockHash>;
    type BlockHashCRHGadget: CRHGadget<Self::BlockHashCRH, Self::InnerScalarField>;
    type BlockHash: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;
    
    /// Masked Merkle tree for the block header root on Proof of Succinct Work (PoSW). Invoked only over `Self::InnerScalarField`.
    type BlockHeaderTreeCRH: CRH<Output = Self::BlockHeaderRoot>;
    type BlockHeaderTreeCRHGadget: MaskedCRHGadget<<Self::BlockHeaderTreeParameters as MerkleParameters>::H, Self::InnerScalarField, OutputGadget = <Self::PoSWMaskPRFGadget as PRFGadget<Self::PoSWMaskPRF, Self::InnerScalarField>>::Seed>;
    type BlockHeaderTreeParameters: MaskedMerkleParameters<H = Self::BlockHeaderTreeCRH>;
    type BlockHeaderRoot: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// CRH scheme for encrypted record ID. Invoked only over `Self::InnerScalarField`.
    type CiphertextIDCRH: CRH<Output = Self::CiphertextID>;
    type CiphertextIDCRHGadget: CRHGadget<Self::CiphertextIDCRH, Self::InnerScalarField>;
    type CiphertextID: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// Commitment scheme for records. Invoked only over `Self::InnerScalarField`.
    type CommitmentScheme: CommitmentScheme<Randomness = Self::CommitmentRandomness, Output = Self::Commitment>;
    type CommitmentGadget: CommitmentGadget<Self::CommitmentScheme, Self::InnerScalarField>;
    type CommitmentRandomness: Copy + Clone + Debug + Display + Default + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + UniformRand + Sync + Send;
    type Commitment: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Debug + Display + Default + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// Merkle tree scheme for the commitments root on the ledger. Invoked only over `Self::InnerScalarField`.
    type CommitmentsTreeCRH: CRH<Output = Self::CommitmentsRoot>;
    type CommitmentsTreeCRHGadget: CRHGadget<Self::CommitmentsTreeCRH, Self::InnerScalarField>;
    type CommitmentsTreeParameters: MerkleParameters<H = Self::CommitmentsTreeCRH>;
    type CommitmentsRoot: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// CRH for deriving function IDs. Invoked only over `Self::OuterScalarField`.
    type FunctionIDCRH: CRH<Output = Self::FunctionID>;
    type FunctionIDCRHGadget: CRHGadget<Self::FunctionIDCRH, Self::OuterScalarField>;
    type FunctionID: ToConstraintField<Self::OuterScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// Crypto hash for deriving the function inputs digest. Invoked only over `Self::InnerScalarField`.
    type FunctionInputsCRH: CRH<Output = Self::FunctionInputsDigest>;
    type FunctionInputsCRHGadget: CRHGadget<Self::FunctionInputsCRH, Self::InnerScalarField>;
    type FunctionInputsDigest: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;
    
    /// CRH for hash of the `Self::InnerSNARK` verifying keys. Invoked only over `Self::OuterScalarField`.
    type InnerCircuitIDCRH: CRH<Output = Self::InnerCircuitID>;
    type InnerCircuitIDCRHGadget: CRHGadget<Self::InnerCircuitIDCRH, Self::OuterScalarField>;
    type InnerCircuitID: ToConstraintField<Self::OuterScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// Merkle tree scheme for the local commitments root in transitions. Invoked only over `Self::InnerScalarField`.
    type LocalCommitmentsTreeCRH: CRH<Output = Self::LocalCommitmentsRoot>;
    type LocalCommitmentsTreeCRHGadget: CRHGadget<Self::LocalCommitmentsTreeCRH, Self::InnerScalarField>;
    type LocalCommitmentsTreeParameters: MerkleParameters<H = Self::LocalCommitmentsTreeCRH>;
    type LocalCommitmentsRoot: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// Schemes for PoSW. Invoked only over `Self::InnerScalarField`.
    type PoSWMaskPRF: PRF<Input = Vec<Self::InnerScalarField>, Seed = Self::BlockHeaderRoot, Output = Self::InnerScalarField>;
    type PoSWMaskPRFGadget: PRFGadget<Self::PoSWMaskPRF, Self::InnerScalarField>;
    type PoSW: PoSWScheme<Self>;
    
    /// CRH for deriving program IDs. Invoked only over `Self::OuterScalarField`.
    type ProgramFunctionsTreeCRH: CRH<Output = Self::ProgramID>;
    type ProgramFunctionsTreeCRHGadget: CRHGadget<Self::ProgramFunctionsTreeCRH, Self::OuterScalarField>;
    type ProgramFunctionsTreeParameters: MerkleParameters<H = Self::ProgramFunctionsTreeCRH>;
    type ProgramID: ToConstraintField<Self::OuterScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;
    
    /// PRF for computing serial numbers. Invoked only over `Self::InnerScalarField`.
    // TODO (howardwu): TEMPORARY - Revisit Vec<Self::SerialNumberNonce> after upgrading serial number construction.
    type SerialNumberPRF: PRF<Input = Vec<Self::SerialNumber>, Seed = Self::InnerScalarField, Output = Self::SerialNumber>;
    type SerialNumberPRFGadget: PRFGadget<Self::SerialNumberPRF, Self::InnerScalarField>;
    type SerialNumber: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Debug + Display + Default + ToBytes + FromBytes + Serialize + DeserializeOwned + UniformRand + PartialEq + Eq + Hash + Sync + Send;

    /// Merkle tree scheme for the serial numbers root. Invoked only over `Self::InnerScalarField`.
    type SerialNumbersTreeCRH: CRH<Output = Self::SerialNumbersRoot>;
    type SerialNumbersTreeParameters: MerkleParameters<H = Self::SerialNumbersTreeCRH>;
    type SerialNumbersRoot: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// CRH scheme for computing the transaction ID. Invoked only over `Self::InnerScalarField`.
    type TransactionIDCRH: CRH<Output = Self::TransactionID>;
    type TransactionID: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// CRH scheme for computing the block transactions root. Invoked only over `Self::InnerScalarField`.
    type TransactionsTreeCRH: CRH<Output = Self::TransactionsRoot>;
    type TransactionsTreeParameters: MerkleParameters<H = Self::TransactionsTreeCRH>;
    type TransactionsRoot: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    /// CRH scheme for computing the transition ID. Invoked only over `Self::InnerScalarField`.
    type TransitionIDCRH: CRH<Output = Self::TransitionID>;
    type TransitionIDCRHGadget: CRHGadget<Self::TransitionIDCRH, Self::InnerScalarField>;
    type TransitionID: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + Serialize + DeserializeOwned + PartialEq + Eq + Hash + Sync + Send;

    fn account_encryption_scheme() -> &'static Self::AccountEncryptionScheme;
    fn account_signature_scheme() -> &'static Self::AccountSignatureScheme;
    fn block_hash_crh() -> &'static Self::BlockHashCRH;
    fn block_header_tree_parameters() -> &'static Self::BlockHeaderTreeParameters;
    fn ciphertext_id_crh() -> &'static Self::CiphertextIDCRH;
    fn commitment_scheme() -> &'static Self::CommitmentScheme;
    fn commitments_tree_parameters() -> &'static Self::CommitmentsTreeParameters;
    fn function_id_crh() -> &'static Self::FunctionIDCRH;
    fn inner_circuit_id_crh() -> &'static Self::InnerCircuitIDCRH;
    fn local_commitments_tree_parameters() -> &'static Self::LocalCommitmentsTreeParameters;
    fn program_functions_tree_parameters() -> &'static Self::ProgramFunctionsTreeParameters;
    fn serial_numbers_tree_parameters() -> &'static Self::SerialNumbersTreeParameters;
    fn transaction_id_crh() -> &'static Self::TransactionIDCRH;
    fn transactions_tree_parameters() -> &'static Self::TransactionsTreeParameters;
    fn transition_id_crh() -> &'static Self::TransitionIDCRH;

    fn inner_circuit_id() -> &'static Self::InnerCircuitID;
    fn inner_proving_key() -> &'static <Self::InnerSNARK as SNARK>::ProvingKey;
    fn inner_verifying_key() -> &'static <Self::InnerSNARK as SNARK>::VerifyingKey;

    fn noop_program() -> &'static Program<Self>;
    fn noop_program_id() -> &'static Self::ProgramID;
    fn noop_program_path() -> &'static MerklePath<Self::ProgramFunctionsTreeParameters>;
    fn noop_function_id() -> &'static Self::FunctionID;
    fn noop_circuit_proving_key() -> &'static <Self::ProgramSNARK as SNARK>::ProvingKey;
    fn noop_circuit_verifying_key() -> &'static <Self::ProgramSNARK as SNARK>::VerifyingKey;

    fn outer_proving_key() -> &'static <Self::OuterSNARK as SNARK>::ProvingKey;
    fn outer_verifying_key() -> &'static <Self::OuterSNARK as SNARK>::VerifyingKey;

    fn posw_proving_key() -> &'static <Self::PoswSNARK as SNARK>::ProvingKey;
    fn posw_verifying_key() -> &'static <Self::PoswSNARK as SNARK>::VerifyingKey;
    fn posw() -> &'static Self::PoSW;

    fn genesis_block() -> &'static Block<Self>;

    /// Returns the function ID given a program function verifying key.
    fn function_id(
        verifying_key: &<Self::ProgramSNARK as SNARK>::VerifyingKey,
    ) -> Result<Self::FunctionID> {
        Ok(Self::function_id_crh().hash_bits(&verifying_key.to_minimal_bits())?)
    }

    /// Returns the program SRS for Aleo applications.
    fn program_srs<R: Rng + CryptoRng>(
        rng: &mut R,
    ) -> Rc<RefCell<SRS<R, <Self::ProgramSNARK as SNARK>::UniversalSetupParameters>>>;
}
