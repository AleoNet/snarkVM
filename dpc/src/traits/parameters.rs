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

use crate::{InnerCircuitVerifierInput, OuterCircuitVerifierInput, ProgramLocalData};
use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, prelude::*};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::{PrimeField, ToConstraintField};
use snarkvm_gadgets::{
    traits::algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget},
    SNARKVerifierGadget,
};
use snarkvm_utilities::{
    fmt::{Debug, Display},
    hash::Hash,
    CanonicalDeserialize,
    CanonicalSerialize,
    FromBytes,
    ToBytes,
};

use anyhow::Result;
use rand::{CryptoRng, Rng};

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
    /// SNARK Verifier gadget for the inner circuit.
    type InnerSNARKGadget: SNARKVerifierGadget<Self::InnerSNARK>;

    /// SNARK for proof-verification checks.
    type OuterSNARK: SNARK<
        ScalarField = Self::OuterScalarField,
        BaseField = Self::OuterBaseField,
        VerifierInput = OuterCircuitVerifierInput<Self>,
    >;

    /// Program SNARK for Aleo applications.
    type ProgramSNARK: SNARK<
        ScalarField = Self::InnerScalarField,
        BaseField = Self::OuterScalarField,
        VerifierInput = ProgramLocalData<Self>,
    >;
    /// Program SNARK verifier gadget for Aleo applications.
    type ProgramSNARKGadget: SNARKVerifierGadget<Self::ProgramSNARK>;

    /// Commitment scheme for account contents. Invoked only over `Self::InnerScalarField`.
    type AccountCommitmentScheme: CommitmentScheme<Output = Self::AccountCommitment>;
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
    type AccountEncryptionScheme: EncryptionScheme;
    type AccountEncryptionGadget: EncryptionGadget<Self::AccountEncryptionScheme, Self::InnerScalarField>;

    /// Signature scheme for delegated compute. Invoked only over `Self::InnerScalarField`.
    type AccountSignatureScheme: SignatureScheme<PublicKey = Self::AccountSignaturePublicKey>;
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
    type EncryptedRecordCRH: CRH<Output = Self::EncryptedRecordDigest>;
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

    /// CRH for hash of the `Self::InnerSNARK` verifying keys.
    /// This is invoked only on the larger curve.
    type InnerCircuitIDCRH: CRH<Output = Self::InnerCircuitIDCRHDigest>;
    type InnerCircuitIDCRHGadget: CRHGadget<Self::InnerCircuitIDCRH, Self::OuterScalarField>;
    type InnerCircuitIDCRHDigest: ToConstraintField<Self::OuterScalarField>
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

    /// CRH and commitment scheme for committing to program input. Invoked inside
    /// `Self::InnerSNARK` and every program SNARK.
    type LocalDataCommitmentScheme: CommitmentScheme;
    type LocalDataCommitmentGadget: CommitmentGadget<Self::LocalDataCommitmentScheme, Self::InnerScalarField>;

    type LocalDataCRH: CRH<Output = Self::LocalDataDigest>;
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
    type ProgramCommitmentScheme: CommitmentScheme<Output = Self::ProgramCommitment>;
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

    /// Program selector tree instantiation for the program ids.
    type ProgramSelectorTreeCRH: CRH<Output = Self::ProgramSelectorTreeDigest>;
    type ProgramSelectorTreeCRHGadget: CRHGadget<Self::ProgramSelectorTreeCRH, Self::OuterScalarField>;
    type ProgramSelectorTreeDigest: ToConstraintField<Self::OuterScalarField>
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
    type ProgramSelectorTreeParameters: LoadableMerkleParameters<H = Self::ProgramSelectorTreeCRH>;

    /// PRF for computing serial numbers. Invoked only over `Self::InnerScalarField`.
    type PRF: PRF;
    type PRFGadget: PRFGadget<Self::PRF, Self::InnerScalarField>;

    /// Commitment scheme for record contents. Invoked only over `Self::InnerScalarField`.
    type RecordCommitmentScheme: CommitmentScheme<Output = Self::RecordCommitment>;
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

    /// Record commitment tree instantiation.
    type RecordCommitmentTreeCRH: CRH<Output = Self::RecordCommitmentTreeDigest>;
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

    /// Record serial number tree instantiation.
    type RecordSerialNumberTreeCRH: CRH<Output = Self::RecordSerialNumberTreeDigest>;
    type RecordSerialNumberTreeDigest: ToConstraintField<Self::InnerScalarField>
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
    type RecordSerialNumberTreeParameters: LoadableMerkleParameters<H = Self::RecordSerialNumberTreeCRH>;

    /// CRH for computing the serial number nonce. Invoked only over `Self::InnerScalarField`.
    type SerialNumberNonceCRH: CRH;
    type SerialNumberNonceCRHGadget: CRHGadget<Self::SerialNumberNonceCRH, Self::InnerScalarField>;

    fn account_commitment_scheme() -> &'static Self::AccountCommitmentScheme;
    fn account_encryption_scheme() -> &'static Self::AccountEncryptionScheme;
    fn account_signature_scheme() -> &'static Self::AccountSignatureScheme;

    fn encrypted_record_crh() -> &'static Self::EncryptedRecordCRH;

    fn inner_circuit_id_crh() -> &'static Self::InnerCircuitIDCRH;

    fn local_data_commitment_scheme() -> &'static Self::LocalDataCommitmentScheme;

    fn local_data_crh() -> &'static Self::LocalDataCRH;

    fn program_commitment_scheme() -> &'static Self::ProgramCommitmentScheme;

    fn program_id_crh() -> &'static Self::ProgramIDCRH;

    fn program_selector_tree_crh() -> &'static Self::ProgramSelectorTreeCRH;
    fn program_selector_tree_parameters() -> &'static Self::ProgramSelectorTreeParameters;

    fn record_commitment_scheme() -> &'static Self::RecordCommitmentScheme;

    fn record_commitment_tree_crh() -> &'static Self::RecordCommitmentTreeCRH;
    fn record_commitment_tree_parameters() -> &'static Self::RecordCommitmentTreeParameters;

    fn record_serial_number_tree_crh() -> &'static Self::RecordSerialNumberTreeCRH;
    fn record_serial_number_tree_parameters() -> &'static Self::RecordSerialNumberTreeParameters;

    fn serial_number_nonce_crh() -> &'static Self::SerialNumberNonceCRH;

    fn inner_circuit_proving_key(is_prover: bool) -> &'static Option<<Self::InnerSNARK as SNARK>::ProvingKey>;
    fn inner_circuit_verifying_key() -> &'static <Self::InnerSNARK as SNARK>::VerifyingKey;

    fn noop_program_proving_key() -> &'static <Self::ProgramSNARK as SNARK>::ProvingKey;
    fn noop_program_verifying_key() -> &'static <Self::ProgramSNARK as SNARK>::VerifyingKey;

    fn outer_circuit_proving_key(is_prover: bool) -> &'static Option<<Self::OuterSNARK as SNARK>::ProvingKey>;
    fn outer_circuit_verifying_key() -> &'static <Self::OuterSNARK as SNARK>::VerifyingKey;

    /// Returns the program SRS for Aleo applications.
    fn program_srs<R: Rng + CryptoRng>(
        rng: &mut R,
    ) -> Result<SRS<R, <Self::ProgramSNARK as SNARK>::UniversalSetupParameters>>;
}
