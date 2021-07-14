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

use crate::account::ACCOUNT_COMMITMENT_INPUT;
use snarkvm_algorithms::traits::{CommitmentScheme, EncryptionScheme, SignatureScheme, CRH, PRF};
use snarkvm_curves::PairingEngine;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::traits::algorithms::{CRHGadget, CommitmentGadget, EncryptionGadget, PRFGadget, SignatureGadget};

pub trait DPCComponents: 'static + Sized {
    const NETWORK_ID: u8;

    const NUM_INPUT_RECORDS: usize;
    const NUM_OUTPUT_RECORDS: usize;
    const NUM_TOTAL_RECORDS: usize = Self::NUM_INPUT_RECORDS + Self::NUM_OUTPUT_RECORDS;

    type InnerCurve: PairingEngine;
    type OuterCurve: PairingEngine;

    type InnerScalarField: PrimeField;
    type OuterScalarField: PrimeField;

    /// Encryption scheme for account records.
    type AccountEncryption: EncryptionScheme;
    type AccountEncryptionGadget: EncryptionGadget<Self::AccountEncryption, Self::InnerScalarField>;

    /// Commitment scheme for account contents. Invoked only over `Self::InnerScalarField`.
    type AccountCommitment: CommitmentScheme;
    type AccountCommitmentGadget: CommitmentGadget<Self::AccountCommitment, Self::InnerScalarField>;

    /// Signature scheme for delegated compute.
    type AccountSignature: SignatureScheme;
    type AccountSignatureGadget: SignatureGadget<Self::AccountSignature, Self::InnerScalarField>;

    /// CRH for the encrypted record.
    type EncryptedRecordCRH: CRH;
    type EncryptedRecordCRHGadget: CRHGadget<Self::EncryptedRecordCRH, Self::InnerScalarField>;

    /// CRH for hash of the `Self::InnerSNARK` verification keys.
    /// This is invoked only on the larger curve.
    type InnerCircuitIDCRH: CRH;
    type InnerCircuitIDCRHGadget: CRHGadget<Self::InnerCircuitIDCRH, Self::OuterScalarField>;

    /// CRH and commitment scheme for committing to program input. Invoked inside
    /// `Self::InnerSNARK` and every program SNARK.
    type LocalDataCRH: CRH;
    type LocalDataCRHGadget: CRHGadget<Self::LocalDataCRH, Self::InnerScalarField>;
    type LocalDataCommitment: CommitmentScheme;
    type LocalDataCommitmentGadget: CommitmentGadget<Self::LocalDataCommitment, Self::InnerScalarField>;

    /// CRH for hashes of birth and death verification keys.
    /// This is invoked only on the larger curve.
    type ProgramVerificationKeyCRH: CRH;
    type ProgramVerificationKeyCRHGadget: CRHGadget<Self::ProgramVerificationKeyCRH, Self::OuterScalarField>;

    /// Commitment scheme for committing to hashes of birth and death verification keys
    type ProgramVerificationKeyCommitment: CommitmentScheme;
    /// Used to commit to hashes of verification keys on the smaller curve and to decommit hashes
    /// of verification keys on the larger curve
    type ProgramVerificationKeyCommitmentGadget: CommitmentGadget<Self::ProgramVerificationKeyCommitment, Self::InnerScalarField>
        + CommitmentGadget<Self::ProgramVerificationKeyCommitment, Self::OuterScalarField>;

    /// PRF for computing serial numbers. Invoked only over `Self::InnerScalarField`.
    type PRF: PRF;
    type PRFGadget: PRFGadget<Self::PRF, Self::InnerScalarField>;

    /// Commitment scheme for record contents. Invoked only over `Self::InnerScalarField`.
    type RecordCommitment: CommitmentScheme;
    type RecordCommitmentGadget: CommitmentGadget<Self::RecordCommitment, Self::InnerScalarField>;

    /// CRH for computing the serial number nonce. Invoked only over `Self::InnerScalarField`.
    type SerialNumberNonceCRH: CRH;
    type SerialNumberNonceCRHGadget: CRHGadget<Self::SerialNumberNonceCRH, Self::InnerScalarField>;

    /// TODO (howardwu): TEMPORARY FOR PR #251 - Move this into a lazy_static! or Arc'ed context.
    #[inline]
    fn account_commitment() -> Self::AccountCommitment {
        Self::AccountCommitment::setup(ACCOUNT_COMMITMENT_INPUT)
    }
}
