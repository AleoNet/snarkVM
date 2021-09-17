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

use crate::{InnerPublicVariables, NoopProgram, OuterPublicVariables, PublicVariables};
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, prelude::*};
use snarkvm_curves::{AffineCurve, PairingEngine, ProjectiveCurve, TwistedEdwardsParameters};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    traits::algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget},
    GroupGadget,
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
use std::{cell::RefCell, rc::Rc};

#[rustfmt::skip]
pub trait Parameters: 'static + Sized + Clone + Debug + PartialEq + Eq + Send + Sync {
    const NETWORK_ID: u8;

    const NUM_INPUT_RECORDS: usize;
    const NUM_OUTPUT_RECORDS: usize;
    const NUM_TOTAL_RECORDS: usize = Self::NUM_INPUT_RECORDS + Self::NUM_OUTPUT_RECORDS;

    const MEMO_SIZE_IN_BYTES: usize;

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
    type OuterSNARK: SNARK<ScalarField = Self::OuterScalarField, BaseField = Self::OuterBaseField, VerifierInput = OuterPublicVariables<Self>>;

    /// Program SNARK for Aleo applications.
    type ProgramSNARK: SNARK<ScalarField = Self::InnerScalarField, BaseField = Self::OuterScalarField, VerifierInput = PublicVariables<Self>>;
    type ProgramSNARKGadget: SNARKVerifierGadget<Self::ProgramSNARK>;

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
    type AccountSignature: Clone + Debug + Default + ToBytes + FromBytes + Send + Sync + PartialEq + Eq;

    /// CRH for encrypted record identifiers. Invoked only over `Self::InnerScalarField`.
    type EncryptedRecordCRH: CRH<Output = Self::EncryptedRecordDigest>;
    type EncryptedRecordCRHGadget: CRHGadget<Self::EncryptedRecordCRH, Self::InnerScalarField>;
    type EncryptedRecordDigest: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;

    /// CRH for hash of the `Self::InnerSNARK` verifying keys. Invoked only over `Self::OuterScalarField`.
    type InnerCircuitIDCRH: CRH<Output = Self::InnerCircuitID>;
    type InnerCircuitIDCRHGadget: CRHGadget<Self::InnerCircuitIDCRH, Self::OuterScalarField>;
    type InnerCircuitID: ToConstraintField<Self::OuterScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;

    /// Ledger commitments tree instantiation. Invoked only over `Self::InnerScalarField`.
    type LedgerCommitmentsTreeCRH: CRH<Output = Self::LedgerCommitmentsTreeDigest>;
    type LedgerCommitmentsTreeCRHGadget: CRHGadget<Self::LedgerCommitmentsTreeCRH, Self::InnerScalarField>;
    type LedgerCommitmentsTreeDigest: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;
    type LedgerCommitmentsTreeParameters: LoadableMerkleParameters<H = Self::LedgerCommitmentsTreeCRH>;

    /// Ledger serial numbers tree instantiation. Invoked only over `Self::InnerScalarField`.
    type LedgerSerialNumbersTreeCRH: CRH<Output = Self::LedgerSerialNumbersTreeDigest>;
    type LedgerSerialNumbersTreeDigest: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;
    type LedgerSerialNumbersTreeParameters: LoadableMerkleParameters<H = Self::LedgerSerialNumbersTreeCRH>;

    /// CRH and commitment scheme for committing to program input. Invoked inside `Self::InnerSNARK` and every program SNARK.
    type LocalDataCommitmentScheme: CommitmentScheme;
    type LocalDataCommitmentGadget: CommitmentGadget<Self::LocalDataCommitmentScheme, Self::InnerScalarField>;
    type LocalDataCRH: CRH<Output = Self::LocalDataRoot>;
    type LocalDataCRHGadget: CRHGadget<Self::LocalDataCRH, Self::InnerScalarField>;
    type LocalDataRoot: ToConstraintField<Self::InnerScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;

    /// Commitment scheme for committing to program IDs over `Self::InnerScalarField` and to decommit program IDs over `Self::OuterScalarField`.
    type ProgramCommitmentScheme: CommitmentScheme<Output = Self::ProgramCommitment>;
    type ProgramCommitmentGadget: CommitmentGadget<Self::ProgramCommitmentScheme, Self::InnerScalarField>
        + CommitmentGadget<Self::ProgramCommitmentScheme, Self::OuterScalarField>;
    type ProgramCommitment: ToConstraintField<Self::InnerScalarField> + Clone + Default + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;

    /// CRH for deriving program circuit IDs. Invoked only over `Self::OuterScalarField`.
    type ProgramCircuitIDCRH: CRH<Output = Self::ProgramCircuitID>;
    type ProgramCircuitIDCRHGadget: CRHGadget<Self::ProgramCircuitIDCRH, Self::OuterScalarField>;
    type ProgramCircuitID: ToConstraintField<Self::OuterScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;

    /// CRH for deriving program IDs. Invoked only over `Self::OuterScalarField`.
    type ProgramCircuitIDTreeCRH: CRH<Output = Self::ProgramCircuitIDTreeDigest>;
    type ProgramCircuitIDTreeCRHGadget: CRHGadget<Self::ProgramCircuitIDTreeCRH, Self::OuterScalarField>;
    type ProgramCircuitIDTreeDigest: ToConstraintField<Self::OuterScalarField> + Copy + Clone + Default + Debug + Display + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;
    type ProgramCircuitTreeParameters: LoadableMerkleParameters<H = Self::ProgramCircuitIDTreeCRH>;

    /// Commitment scheme for record contents. Invoked only over `Self::InnerScalarField`.
    type RecordCommitmentScheme: CommitmentScheme<Output = Self::RecordCommitment>;
    type RecordCommitmentGadget: CommitmentGadget<Self::RecordCommitmentScheme, Self::InnerScalarField>;
    type RecordCommitment: ToConstraintField<Self::InnerScalarField> + Clone + Debug + Default + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;

    /// CRH for computing the serial number nonce. Invoked only over `Self::InnerScalarField`.
    type SerialNumberNonceCRH: CRH<Output = Self::SerialNumberNonce>;
    type SerialNumberNonceCRHGadget: CRHGadget<Self::SerialNumberNonceCRH, Self::InnerScalarField>;
    type SerialNumberNonce: ToConstraintField<Self::InnerScalarField> + Clone + Default + Debug + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;

    /// PRF for computing serial numbers. Invoked only over `Self::InnerScalarField`.
    // TODO (howardwu): TEMPORARY - Revisit Vec<Self::SerialNumberNonce> after upgrading serial number construction.
    type SerialNumberPRF: PRF<Input = Vec<Self::SerialNumberNonce>, Seed = Self::InnerScalarField, Output = Self::SerialNumber>;
    type SerialNumberPRFGadget: PRFGadget<Self::SerialNumberPRF, Self::InnerScalarField>;
    type SerialNumber: ToConstraintField<Self::InnerScalarField> + Clone + Debug + Default + ToBytes + FromBytes + PartialEq + Eq + Hash + Sync + Send;
    
    /// CRH for computing the transaction ID.
    type TransactionIDCRH: CRH;

    fn account_encryption_scheme() -> &'static Self::AccountEncryptionScheme;
    fn account_signature_scheme() -> &'static Self::AccountSignatureScheme;

    fn encrypted_record_crh() -> &'static Self::EncryptedRecordCRH;
    fn inner_circuit_id_crh() -> &'static Self::InnerCircuitIDCRH;
    fn local_data_commitment_scheme() -> &'static Self::LocalDataCommitmentScheme;
    fn local_data_crh() -> &'static Self::LocalDataCRH;
    fn program_commitment_scheme() -> &'static Self::ProgramCommitmentScheme;

    fn program_circuit_id_crh() -> &'static Self::ProgramCircuitIDCRH;
    fn program_circuit_id_tree_crh() -> &'static Self::ProgramCircuitIDTreeCRH;
    fn program_circuit_tree_parameters() -> &'static Self::ProgramCircuitTreeParameters;

    fn record_commitment_scheme() -> &'static Self::RecordCommitmentScheme;

    fn ledger_commitments_tree_crh() -> &'static Self::LedgerCommitmentsTreeCRH;
    fn ledger_commitments_tree_parameters() -> &'static Self::LedgerCommitmentsTreeParameters;

    fn ledger_serial_numbers_tree_crh() -> &'static Self::LedgerSerialNumbersTreeCRH;
    fn ledger_serial_numbers_tree_parameters() -> &'static Self::LedgerSerialNumbersTreeParameters;

    fn serial_number_nonce_crh() -> &'static Self::SerialNumberNonceCRH;
    
    fn transaction_id_crh() -> &'static Self::TransactionIDCRH;

    fn inner_circuit_id() -> &'static Self::InnerCircuitID;
    fn inner_circuit_proving_key(is_prover: bool) -> &'static Option<<Self::InnerSNARK as SNARK>::ProvingKey>;
    fn inner_circuit_verifying_key() -> &'static <Self::InnerSNARK as SNARK>::VerifyingKey;

    fn noop_program() -> &'static NoopProgram<Self>;
    fn noop_circuit_id() -> &'static Self::ProgramCircuitID;
    fn noop_circuit_proving_key() -> &'static <Self::ProgramSNARK as SNARK>::ProvingKey;
    fn noop_circuit_verifying_key() -> &'static <Self::ProgramSNARK as SNARK>::VerifyingKey;

    fn outer_circuit_proving_key(is_prover: bool) -> &'static Option<<Self::OuterSNARK as SNARK>::ProvingKey>;
    fn outer_circuit_verifying_key() -> &'static <Self::OuterSNARK as SNARK>::VerifyingKey;

    /// Returns the program circuit ID given a program circuit verifying key.
    fn program_circuit_id(
        verifying_key: &<Self::ProgramSNARK as SNARK>::VerifyingKey,
    ) -> Result<Self::ProgramCircuitID> {
        Ok(Self::program_circuit_id_crh().hash_bits(&verifying_key.to_minimal_bits())?)
    }

    /// Returns the program SRS for Aleo applications.
    fn program_srs<R: Rng + CryptoRng>(
        rng: &mut R,
    ) -> Rc<RefCell<SRS<R, <Self::ProgramSNARK as SNARK>::UniversalSetupParameters>>>;
}
