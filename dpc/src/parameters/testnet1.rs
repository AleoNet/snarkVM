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

use crate::{
    account::{ACCOUNT_COMMITMENT_INPUT, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT},
    InnerPublicVariables,
    Network,
    OuterPublicVariables,
    Parameters,
    PublicVariables,
    Transaction,
    DPC,
};
use snarkvm_algorithms::{
    commitment::{BHPCompressedCommitment, Blake2sCommitment},
    crh::BHPCompressedCRH,
    crypto_hash::PoseidonCryptoHash,
    define_merkle_tree_parameters,
    encryption::ECIESPoseidonEncryption,
    prelude::*,
    prf::Blake2s,
    signature::SchnorrCompressed,
    snark::groth16::Groth16,
};
use snarkvm_curves::{
    bls12_377::Bls12_377,
    bw6_761::BW6_761,
    edwards_bls12::{EdwardsParameters, EdwardsProjective as EdwardsBls12},
    PairingEngine,
};
use snarkvm_fields::ToConstraintField;
use snarkvm_gadgets::{
    algorithms::{
        commitment::{BHPCompressedCommitmentGadget, Blake2sCommitmentGadget},
        crh::BHPCompressedCRHGadget,
        crypto_hash::PoseidonCryptoHashGadget,
        encryption::ECIESPoseidonEncryptionGadget,
        prf::Blake2sGadget,
        signature::SchnorrCompressedGadget,
        snark::Groth16VerifierGadget,
    },
    curves::{bls12_377::PairingGadget, edwards_bls12::EdwardsBls12Gadget},
};
use snarkvm_parameters::{testnet1::*, Parameter};
use snarkvm_utilities::FromBytes;

use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use std::{cell::RefCell, rc::Rc};

macro_rules! dpc_setup {
    ($fn_name: ident, $static_name: ident, $type_name: ident, $setup_msg: expr) => {
        #[inline]
        fn $fn_name() -> &'static Self::$type_name {
            static $static_name: OnceCell<<Testnet1Parameters as Parameters>::$type_name> = OnceCell::new();
            $static_name.get_or_init(|| Self::$type_name::setup($setup_msg))
        }
    };
}

pub type Testnet1DPC = DPC<Testnet1Parameters>;
pub type Testnet1Transaction = Transaction<Testnet1Parameters>;

define_merkle_tree_parameters!(
    ProgramIDMerkleTreeParameters,
    <Testnet1Parameters as Parameters>::ProgramCircuitIDCRH,
    8
);

define_merkle_tree_parameters!(
    CommitmentMerkleTreeParameters,
    <Testnet1Parameters as Parameters>::RecordCommitmentTreeCRH,
    32
);

define_merkle_tree_parameters!(
    SerialNumberMerkleTreeParameters,
    <Testnet1Parameters as Parameters>::RecordSerialNumberTreeCRH,
    32
);

pub struct Testnet1Parameters;

#[rustfmt::skip]
impl Parameters for Testnet1Parameters {
    const NETWORK_ID: u8 = Network::Testnet1.id();

    const NUM_INPUT_RECORDS: usize = 2;
    const NUM_OUTPUT_RECORDS: usize = 2;

    type InnerCurve = Bls12_377;
    type OuterCurve = BW6_761;

    type InnerScalarField = <Self::InnerCurve as PairingEngine>::Fr;
    type OuterScalarField = <Self::OuterCurve as PairingEngine>::Fr;
    type OuterBaseField = <Self::OuterCurve as PairingEngine>::Fq;

    type InnerSNARK = Groth16<Self::InnerCurve, InnerPublicVariables<Testnet1Parameters>>;
    type InnerSNARKGadget = Groth16VerifierGadget<Self::InnerCurve, PairingGadget>;

    type OuterSNARK = Groth16<Self::OuterCurve, OuterPublicVariables<Testnet1Parameters>>;

    type ProgramSNARK = Groth16<Self::InnerCurve, PublicVariables<Self>>;
    type ProgramSNARKGadget = Groth16VerifierGadget<Self::InnerCurve, PairingGadget>;

    type AccountCommitmentScheme = BHPCompressedCommitment<EdwardsBls12, 33, 48>;
    type AccountCommitmentGadget = BHPCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 33, 48>;
    type AccountCommitment = <Self::AccountCommitmentScheme as CommitmentScheme>::Output;

    type AccountEncryptionScheme = ECIESPoseidonEncryption<EdwardsParameters>;
    type AccountEncryptionGadget = ECIESPoseidonEncryptionGadget<EdwardsParameters, Self::InnerScalarField>;

    type AccountSignatureScheme = SchnorrCompressed<EdwardsParameters>;
    type AccountSignatureGadget = SchnorrCompressedGadget<EdwardsParameters, Self::InnerScalarField>;
    type AccountSignaturePublicKey = <Self::AccountSignatureScheme as SignatureScheme>::PublicKey;
    type AccountSignature = <Self::AccountSignatureScheme as SignatureScheme>::Signature;

    type EncryptedRecordCRH = PoseidonCryptoHash<Self::InnerScalarField, 4, false>;
    type EncryptedRecordCRHGadget = PoseidonCryptoHashGadget<Self::InnerScalarField, 4, false>;
    type EncryptedRecordDigest = <Self::EncryptedRecordCRH as CRH>::Output;

    type InnerCircuitIDCRH = PoseidonCryptoHash<Self::OuterScalarField, 4, false>;
    type InnerCircuitIDCRHGadget = PoseidonCryptoHashGadget<Self::OuterScalarField, 4, false>;
    type InnerCircuitID = <Self::InnerCircuitIDCRH as CRH>::Output;

    type LocalDataCommitmentScheme = BHPCompressedCommitment<EdwardsBls12, 24, 62>;
    type LocalDataCommitmentGadget = BHPCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 24, 62>;

    type LocalDataCRH = BHPCompressedCRH<EdwardsBls12, 16, 32>;
    type LocalDataCRHGadget = BHPCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 16, 32>;
    type LocalDataRoot = <Self::LocalDataCRH as CRH>::Output;

    type PRF = Blake2s;
    type PRFGadget = Blake2sGadget;

    type ProgramCommitmentScheme = Blake2sCommitment;
    type ProgramCommitmentGadget = Blake2sCommitmentGadget;
    type ProgramCommitment = <Self::ProgramCommitmentScheme as CommitmentScheme>::Output;

    type ProgramCircuitIDCRH = PoseidonCryptoHash<Self::OuterScalarField, 4, false>;
    type ProgramCircuitIDCRHGadget = PoseidonCryptoHashGadget<Self::OuterScalarField, 4, false>;
    type ProgramCircuitID = <Self::ProgramCircuitIDCRH as CRH>::Output;
    type ProgramCircuitTreeParameters = ProgramIDMerkleTreeParameters;
    
    type RecordCommitmentScheme = BHPCompressedCommitment<EdwardsBls12, 48, 50>;
    type RecordCommitmentGadget = BHPCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 48, 50>;
    type RecordCommitment = <Self::RecordCommitmentScheme as CommitmentScheme>::Output;

    type RecordCommitmentTreeCRH = BHPCompressedCRH<EdwardsBls12, 8, 32>;
    type RecordCommitmentTreeCRHGadget = BHPCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 8, 32>;
    type RecordCommitmentTreeDigest = <Self::RecordCommitmentTreeCRH as CRH>::Output;
    type RecordCommitmentTreeParameters = CommitmentMerkleTreeParameters;

    type RecordSerialNumberTreeCRH = BHPCompressedCRH<EdwardsBls12, 8, 32>;
    type RecordSerialNumberTreeDigest = <Self::RecordSerialNumberTreeCRH as CRH>::Output;
    type RecordSerialNumberTreeParameters = SerialNumberMerkleTreeParameters;

    type SerialNumberNonceCRH = BHPCompressedCRH<EdwardsBls12, 32, 63>;
    type SerialNumberNonceCRHGadget = BHPCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 32, 63>;
    type SerialNumberNonce = <Self::SerialNumberNonceCRH as CRH>::Output;
    
    dpc_setup!{account_commitment_scheme, ACCOUNT_COMMITMENT_SCHEME, AccountCommitmentScheme, ACCOUNT_COMMITMENT_INPUT} // TODO (howardwu): Rename to "AleoAccountCommitmentScheme0".
    dpc_setup!{account_encryption_scheme, ACCOUNT_ENCRYPTION_SCHEME, AccountEncryptionScheme, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT}
    dpc_setup!{account_signature_scheme, ACCOUNT_SIGNATURE_SCHEME, AccountSignatureScheme, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT}
    dpc_setup!{encrypted_record_crh, ENCRYPTED_RECORD_CRH, EncryptedRecordCRH, "AleoEncryptedRecordCRH0"}
    dpc_setup!{inner_circuit_id_crh, INNER_CIRCUIT_ID_CRH, InnerCircuitIDCRH, "AleoInnerCircuitIDCRH0"}
    dpc_setup!{local_data_commitment_scheme, LOCAL_DATA_COMMITMENT_SCHEME, LocalDataCommitmentScheme, "AleoLocalDataCommitment0"} // TODO (howardwu): Rename to "AleoLocalDataCommitmentScheme0".
    dpc_setup!{local_data_crh, LOCAL_DATA_CRH, LocalDataCRH, "AleoLocalDataCRH0"}
    dpc_setup!{program_commitment_scheme, PROGRAM_COMMITMENT_SCHEME, ProgramCommitmentScheme, "AleoProgramIDCommitment0"} // TODO (howardwu): Rename to "AleoProgramCommitmentScheme0".
    dpc_setup!{program_circuit_id_crh, PROGRAM_CIRCUIT_ID_CRH, ProgramCircuitIDCRH, "AleoProgramIDCRH0"} // TODO (howardwu): Rename to "AleoProgramCircuitIDCRH0".
    dpc_setup!{record_commitment_scheme, RECORD_COMMITMENT_SCHEME, RecordCommitmentScheme, "AleoRecordCommitment0"} // TODO (howardwu): Rename to "AleoRecordCommitmentScheme0".
    dpc_setup!{record_commitment_tree_crh, RECORD_COMMITMENT_TREE_CRH, RecordCommitmentTreeCRH, "AleoLedgerMerkleTreeCRH0"} // TODO (howardwu): Rename to "AleoRecordCommitmentTreeCRH0".
    dpc_setup!{record_serial_number_tree_crh, RECORD_COMMITMENT_TREE_CRH, RecordCommitmentTreeCRH, "AleoRecordSerialNumberTreeCRH0"}
    dpc_setup!{serial_number_nonce_crh, SERIAL_NUMBER_NONCE_CRH, SerialNumberNonceCRH, "AleoSerialNumberNonceCRH0"}

    fn inner_circuit_id() -> &'static Self::InnerCircuitID {
        static INNER_CIRCUIT_ID: OnceCell<<Testnet1Parameters as Parameters>::InnerCircuitID> = OnceCell::new();
        INNER_CIRCUIT_ID.get_or_init(|| Self::inner_circuit_id_crh()
            .hash_field_elements(&Self::inner_circuit_verifying_key().to_field_elements().expect("Failed to convert inner circuit verifying key to elements"))
            .expect("Failed to hash inner circuit verifying key elements"))
    }

    dpc_snark_setup_with_mode!{Testnet1Parameters, inner_circuit_proving_key, INNER_CIRCUIT_PROVING_KEY, InnerSNARK, ProvingKey, InnerSNARKPKParameters, "inner circuit proving key"}
    dpc_snark_setup!{Testnet1Parameters, inner_circuit_verifying_key, INNER_CIRCUIT_VERIFYING_KEY, InnerSNARK, VerifyingKey, InnerSNARKVKParameters, "inner circuit verifying key"}

    fn noop_circuit_id() -> &'static Self::ProgramCircuitID {
        static NOOP_CIRCUIT_ID: OnceCell<<Testnet1Parameters as Parameters>::InnerCircuitID> = OnceCell::new();
        NOOP_CIRCUIT_ID.get_or_init(|| Self::program_circuit_id(Self::noop_circuit_verifying_key()).expect("Failed to hash noop circuit verifying key"))
    }
    
    dpc_snark_setup!{Testnet1Parameters, noop_circuit_proving_key, NOOP_CIRCUIT_PROVING_KEY, ProgramSNARK, ProvingKey, NoopProgramSNARKPKParameters, "noop circuit proving key"}
    dpc_snark_setup!{Testnet1Parameters, noop_circuit_verifying_key, NOOP_CIRCUIT_VERIFYING_KEY, ProgramSNARK, VerifyingKey, NoopProgramSNARKVKParameters, "noop circuit verifying key"}

    dpc_snark_setup_with_mode!{Testnet1Parameters, outer_circuit_proving_key, OUTER_CIRCUIT_PROVING_KEY, OuterSNARK, ProvingKey, OuterSNARKPKParameters, "outer circuit proving key"}
    dpc_snark_setup!{Testnet1Parameters, outer_circuit_verifying_key, OUTER_CIRCUIT_VERIFYING_KEY, OuterSNARK, VerifyingKey, OuterSNARKVKParameters, "outer circuit verifying key"}
    
    fn program_circuit_tree_parameters() -> &'static Self::ProgramCircuitTreeParameters {
        static PROGRAM_ID_TREE_PARAMETERS: OnceCell<<Testnet1Parameters as Parameters>::ProgramCircuitTreeParameters> = OnceCell::new();
        PROGRAM_ID_TREE_PARAMETERS.get_or_init(|| Self::ProgramCircuitTreeParameters::from(Self::program_circuit_id_crh().clone()))
    }
    
    fn record_commitment_tree_parameters() -> &'static Self::RecordCommitmentTreeParameters {
        static RECORD_COMMITMENT_TREE_PARAMETERS: OnceCell<<Testnet1Parameters as Parameters>::RecordCommitmentTreeParameters> = OnceCell::new();
        RECORD_COMMITMENT_TREE_PARAMETERS.get_or_init(|| Self::RecordCommitmentTreeParameters::from(Self::record_commitment_tree_crh().clone()))
    }
    
    fn record_serial_number_tree_parameters() -> &'static Self::RecordSerialNumberTreeParameters {
        static RECORD_SERIAL_NUMBER_TREE_PARAMETERS: OnceCell<<Testnet1Parameters as Parameters>::RecordSerialNumberTreeParameters> = OnceCell::new();
        RECORD_SERIAL_NUMBER_TREE_PARAMETERS.get_or_init(|| Self::RecordSerialNumberTreeParameters::from(Self::record_serial_number_tree_crh().clone()))
    }

    /// Returns the program SRS for Aleo applications.
    fn program_srs<R: Rng + CryptoRng>(rng: &mut R) -> Rc<RefCell<SRS<R, <Self::ProgramSNARK as SNARK>::UniversalSetupParameters>>> {
        Rc::new(RefCell::new(SRS::CircuitSpecific(rng)))
    }
}
