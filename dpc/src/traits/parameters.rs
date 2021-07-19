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

use crate::{InnerCircuitVerifierInput, OuterCircuitVerifierInput};
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, prelude::*};
use snarkvm_curves::{
    traits::{MontgomeryParameters, ProjectiveCurve, TwistedEdwardsParameters},
    PairingEngine,
};
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    traits::algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget},
    CompressedGroupGadget,
};
use snarkvm_utilities::{
    fmt::{Debug, Display},
    hash::Hash,
    CanonicalDeserialize,
    CanonicalSerialize,
    FromBytes,
    ToBytes,
};

pub trait Parameters: 'static + Sized {
    const NETWORK_ID: u8;

    const NUM_INPUT_RECORDS: usize;
    const NUM_OUTPUT_RECORDS: usize;
    const NUM_TOTAL_RECORDS: usize = Self::NUM_INPUT_RECORDS + Self::NUM_OUTPUT_RECORDS;

    type InnerCurve: PairingEngine;
    type OuterCurve: PairingEngine;

    type InnerScalarField: PrimeField + PoseidonDefaultParametersField;
    type OuterScalarField: PrimeField;
    type OuterBaseField: PrimeField;

    /// SNARK for inner circuit proof generation.
    type InnerSNARK: SNARK<
        ScalarField = Self::InnerScalarField,
        BaseField = Self::OuterScalarField,
        VerifierInput = InnerCircuitVerifierInput<Self>,
    >;
    /// SNARK for proof-verification checks.
    type OuterSNARK: SNARK<
        ScalarField = Self::OuterScalarField,
        BaseField = Self::OuterBaseField,
        VerifierInput = OuterCircuitVerifierInput<Self>,
    >;

    /// Commitment scheme for account contents. Invoked only over `Self::InnerScalarField`.
    type AccountCommitmentScheme: CommitmentScheme<Output = Self::AccountCommitment>
        + ToConstraintField<Self::InnerScalarField>;
    type AccountCommitmentGadget: CommitmentGadget<Self::AccountCommitmentScheme, Self::InnerScalarField>;
    type AccountCommitment: ToConstraintField<Self::InnerScalarField>
        + Clone
        + Debug
        + Default
        + Eq
        + Hash
        + ToBytes
        + FromBytes
        + Sync
        + Send;

    /// Encryption scheme for account records. Invoked only over `Self::InnerScalarField`.
    type AccountEncryptionScheme: EncryptionScheme + ToConstraintField<Self::InnerScalarField>;
    type AccountEncryptionGadget: EncryptionGadget<Self::AccountEncryptionScheme, Self::InnerScalarField>;

    /// Signature scheme for delegated compute. Invoked only over `Self::InnerScalarField`.
    type AccountSignatureScheme: SignatureScheme<PublicKey = Self::AccountSignaturePublicKey>
        + ToConstraintField<Self::InnerScalarField>;
    type AccountSignatureGadget: SignatureGadget<Self::AccountSignatureScheme, Self::InnerScalarField>;
    type AccountSignaturePublicKey: ToConstraintField<Self::InnerScalarField>
        + Clone
        + Debug
        + Default
        + ToBytes
        + FromBytes
        + Hash
        + Eq
        + Send
        + Sync
        + CanonicalSerialize
        + CanonicalDeserialize;

    /// CRH for the encrypted record. Invoked only over `Self::InnerScalarField`.
    type EncryptedRecordCRH: CRH<Output = Self::EncryptedRecordDigest> + ToConstraintField<Self::InnerScalarField>;
    type EncryptedRecordCRHGadget: CRHGadget<Self::EncryptedRecordCRH, Self::InnerScalarField>;
    type EncryptedRecordDigest: ToConstraintField<Self::InnerScalarField>
        + Clone
        + Debug
        + Display
        + ToBytes
        + FromBytes
        + Eq
        + Hash
        + Default
        + Send
        + Sync
        + Copy;

    /// Group and Model Parameters for record encryption
    type EncryptionGroup: ProjectiveCurve;
    type EncryptionGroupGadget: CompressedGroupGadget<Self::EncryptionGroup, Self::InnerScalarField>;
    type EncryptionParameters: MontgomeryParameters + TwistedEdwardsParameters;

    /// CRH for hash of the `Self::InnerSNARK` verifying keys.
    /// This is invoked only on the larger curve.
    type InnerCircuitIDCRH: CRH;
    type InnerCircuitIDCRHGadget: CRHGadget<Self::InnerCircuitIDCRH, Self::OuterScalarField>;

    /// CRH and commitment scheme for committing to program input. Invoked inside
    /// `Self::InnerSNARK` and every program SNARK.
    type LocalDataCommitmentScheme: CommitmentScheme + ToConstraintField<Self::InnerScalarField>;
    type LocalDataCommitmentGadget: CommitmentGadget<Self::LocalDataCommitmentScheme, Self::InnerScalarField>;

    type LocalDataCRH: CRH<Output = Self::LocalDataDigest> + ToConstraintField<Self::InnerScalarField>;
    type LocalDataCRHGadget: CRHGadget<Self::LocalDataCRH, Self::InnerScalarField>;
    type LocalDataDigest: ToConstraintField<Self::InnerScalarField>
        + Clone
        + Debug
        + Display
        + ToBytes
        + FromBytes
        + Eq
        + Hash
        + Default
        + Send
        + Sync
        + Copy;

    /// Commitment scheme for committing to hashes of birth and death verifying keys.
    type ProgramCommitmentScheme: CommitmentScheme<Output = Self::ProgramCommitment>
        + ToConstraintField<Self::InnerScalarField>
        + ToConstraintField<Self::OuterScalarField>;
    /// Used to commit to hashes of verifying keys on the smaller curve and to decommit hashes
    /// of verification keys on the larger curve
    type ProgramCommitmentGadget: CommitmentGadget<Self::ProgramCommitmentScheme, Self::InnerScalarField>
        + CommitmentGadget<Self::ProgramCommitmentScheme, Self::OuterScalarField>;
    type ProgramCommitment: ToConstraintField<Self::InnerScalarField>
        + Clone
        + Debug
        + Default
        + Eq
        + Hash
        + ToBytes
        + FromBytes
        + Sync
        + Send;

    /// CRH for hashes of birth and death verifying keys. Invoked only over `Self::OuterScalarField`.
    type ProgramIDCRH: CRH;
    type ProgramIDCRHGadget: CRHGadget<Self::ProgramIDCRH, Self::OuterScalarField>;

    /// PRF for computing serial numbers. Invoked only over `Self::InnerScalarField`.
    type PRF: PRF;
    type PRFGadget: PRFGadget<Self::PRF, Self::InnerScalarField>;

    /// Commitment scheme for record contents. Invoked only over `Self::InnerScalarField`.
    type RecordCommitmentScheme: CommitmentScheme<Output = Self::RecordCommitment>
        + ToConstraintField<Self::InnerScalarField>;
    type RecordCommitmentGadget: CommitmentGadget<Self::RecordCommitmentScheme, Self::InnerScalarField>;
    type RecordCommitment: ToConstraintField<Self::InnerScalarField>
        + Clone
        + Debug
        + Default
        + Eq
        + Hash
        + ToBytes
        + FromBytes
        + Sync
        + Send;

    /// Record commitment tree instantiation for the ledger digest.
    type RecordCommitmentTreeCRH: CRH<Output = Self::RecordCommitmentTreeDigest>
        + ToConstraintField<Self::InnerScalarField>;
    type RecordCommitmentTreeCRHGadget: CRHGadget<Self::RecordCommitmentTreeCRH, Self::InnerScalarField>;
    type RecordCommitmentTreeDigest: ToConstraintField<Self::InnerScalarField>
        + Clone
        + Debug
        + Display
        + ToBytes
        + FromBytes
        + Eq
        + Hash
        + Default
        + Send
        + Sync
        + Copy;
    type RecordCommitmentTreeParameters: LoadableMerkleParameters<H = Self::RecordCommitmentTreeCRH>;

    /// CRH for computing the serial number nonce. Invoked only over `Self::InnerScalarField`.
    type SerialNumberNonceCRH: CRH + ToConstraintField<Self::InnerScalarField>;
    type SerialNumberNonceCRHGadget: CRHGadget<Self::SerialNumberNonceCRH, Self::InnerScalarField>;

    fn account_commitment_scheme() -> &'static Self::AccountCommitmentScheme;

    fn account_encryption_scheme() -> &'static Self::AccountEncryptionScheme;

    fn account_signature_scheme() -> &'static Self::AccountSignatureScheme;

    fn encrypted_record_crh() -> &'static Self::EncryptedRecordCRH;

    fn inner_circuit_id_crh() -> &'static Self::InnerCircuitIDCRH;

    fn record_commitment_tree_crh() -> &'static Self::RecordCommitmentTreeCRH;

    fn local_data_commitment_scheme() -> &'static Self::LocalDataCommitmentScheme;

    fn local_data_crh() -> &'static Self::LocalDataCRH;

    fn program_commitment_scheme() -> &'static Self::ProgramCommitmentScheme;

    fn program_id_crh() -> &'static Self::ProgramIDCRH;

    fn record_commitment_scheme() -> &'static Self::RecordCommitmentScheme;

    fn record_commitment_tree_parameters() -> &'static Self::RecordCommitmentTreeParameters;

    fn serial_number_nonce_crh() -> &'static Self::SerialNumberNonceCRH;
}
