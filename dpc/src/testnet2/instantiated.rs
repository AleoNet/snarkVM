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
    testnet2::{
        inner_circuit::InnerCircuit,
        inner_circuit_verifier_input::InnerCircuitVerifierInput,
        outer_circuit::OuterCircuit,
        outer_circuit_verifier_input::OuterCircuitVerifierInput,
        program::{NoopCircuit, ProgramLocalData},
        transaction::Transaction,
        LocalData as DPCLocalData,
        Testnet2Components,
        DPC,
    },
    traits::DPCComponents,
};
use snarkvm_algorithms::{
    commitment::{Blake2sCommitment, PedersenCompressedCommitment},
    crh::BoweHopwoodPedersenCompressedCRH,
    define_merkle_tree_parameters,
    encryption::GroupEncryption,
    prf::Blake2s,
    signature::Schnorr,
    snark::groth16::Groth16,
};
use snarkvm_curves::{
    bls12_377::{fq::Fq as Bls12_377Fq, fr::Fr as Bls12_377Fr, Bls12_377},
    bw6_761::BW6_761,
    edwards_bls12::{EdwardsAffine, EdwardsParameters, EdwardsProjective as EdwardsBls},
    edwards_sw6::EdwardsProjective as EdwardsSW,
};
use snarkvm_gadgets::{
    algorithms::{
        commitment::{Blake2sCommitmentGadget, PedersenCompressedCommitmentGadget},
        crh::BoweHopwoodPedersenCompressedCRHGadget,
        encryption::GroupEncryptionGadget,
        prf::Blake2sGadget,
        signature::SchnorrPublicKeyRandomizationGadget,
        snark::Groth16VerifierGadget,
    },
    curves::{bls12_377::PairingGadget, edwards_bls12::EdwardsBlsGadget, edwards_sw6::EdwardsSWGadget},
};
use snarkvm_marlin::{
    constraints::{snark::MarlinSNARK, verifier::MarlinVerificationGadget},
    marlin::MarlinTestnet2Mode,
    FiatShamirAlgebraicSpongeRng,
    PoseidonSponge,
};
use snarkvm_polycommit::marlin_pc::{marlin_kzg10::MarlinKZG10Gadget, MarlinKZG10};

use blake2::Blake2s as Blake2sHash;

pub const NUM_INPUT_RECORDS: usize = 2;
pub const NUM_OUTPUT_RECORDS: usize = 2;

// TODO (raychu86): Optimize windows.

const ACCOUNT_NUM_WINDOWS: usize = 8;
const ACCOUNT_WINDOW_SIZE: usize = 192;

const ENCRYPTED_RECORD_NUM_WINDOWS: usize = 48;
const ENCRYPTED_RECORD_WINDOW_SIZE: usize = 44;

const INNER_CIRCUIT_ID_NUM_WINDOWS: usize = 296;
const INNER_CIRCUIT_ID_WINDOW_SIZE: usize = 63;

const LOCAL_DATA_CRH_NUM_WINDOWS: usize = 16;
const LOCAL_DATA_CRH_WINDOW_SIZE: usize = 32;

const LOCAL_DATA_COMMITMENT_NUM_WINDOWS: usize = 8;
const LOCAL_DATA_COMMITMENT_WINDOW_SIZE: usize = 129;

const PROGRAM_VK_CRH_NUM_WINDOWS: usize = 4096;
const PROGRAM_VK_CRH_WINDOW_SIZE: usize = 80;

const RECORD_NUM_WINDOWS: usize = 8;
const RECORD_WINDOW_SIZE: usize = 233;

const SN_NONCE_NUM_WINDOWS: usize = 32;
const SN_NONCE_WINDOW_SIZE: usize = 63;

const MERKLE_TREE_CRH_NUM_WINDOWS: usize = 8;
const MERKLE_TREE_CRH_WINDOW_SIZE: usize = 32;

define_merkle_tree_parameters!(CommitmentMerkleParameters, MerkleTreeCRH, 32);

pub struct Components;

#[rustfmt::skip]
impl DPCComponents for Components {
    const NUM_INPUT_RECORDS: usize = NUM_INPUT_RECORDS;
    const NUM_OUTPUT_RECORDS: usize = NUM_OUTPUT_RECORDS;

    type InnerField = Bls12_377Fr;
    type OuterField = Bls12_377Fq;
    
    type AccountCommitment = PedersenCompressedCommitment<EdwardsBls, ACCOUNT_NUM_WINDOWS, ACCOUNT_WINDOW_SIZE>;
    type AccountCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
    
    type AccountEncryption = GroupEncryption<EdwardsBls, EdwardsAffine, Blake2sHash>;
    type AccountEncryptionGadget = GroupEncryptionGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
    
    type AccountSignature = Schnorr<EdwardsAffine, Blake2sHash>;
    type AccountSignatureGadget = SchnorrPublicKeyRandomizationGadget<EdwardsAffine, Self::InnerField, EdwardsBlsGadget>;
    
    type EncryptedRecordCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, ENCRYPTED_RECORD_NUM_WINDOWS, ENCRYPTED_RECORD_WINDOW_SIZE>;
    type EncryptedRecordCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
    
    type InnerCircuitIDCRH = BoweHopwoodPedersenCompressedCRH<EdwardsSW, INNER_CIRCUIT_ID_NUM_WINDOWS, INNER_CIRCUIT_ID_WINDOW_SIZE>;
    type InnerCircuitIDCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsSW, Self::OuterField, EdwardsSWGadget>;
    
    type LocalDataCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, LOCAL_DATA_CRH_NUM_WINDOWS, LOCAL_DATA_CRH_WINDOW_SIZE>;
    type LocalDataCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
    
    type LocalDataCommitment = PedersenCompressedCommitment<EdwardsBls, LOCAL_DATA_COMMITMENT_NUM_WINDOWS, LOCAL_DATA_COMMITMENT_WINDOW_SIZE>;
    type LocalDataCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
    
    type PRF = Blake2s;
    type PRFGadget = Blake2sGadget;
    
    type ProgramVerificationKeyCRH = BoweHopwoodPedersenCompressedCRH<EdwardsSW, PROGRAM_VK_CRH_NUM_WINDOWS, PROGRAM_VK_CRH_WINDOW_SIZE>;
    type ProgramVerificationKeyCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsSW, Self::OuterField, EdwardsSWGadget>;
    
    type ProgramVerificationKeyCommitment = Blake2sCommitment;
    type ProgramVerificationKeyCommitmentGadget = Blake2sCommitmentGadget;
    
    type RecordCommitment = PedersenCompressedCommitment<EdwardsBls, RECORD_NUM_WINDOWS, RECORD_WINDOW_SIZE>;
    type RecordCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
    
    type SerialNumberNonceCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, SN_NONCE_NUM_WINDOWS, SN_NONCE_WINDOW_SIZE>;
    type SerialNumberNonceCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
}

impl Testnet2Components for Components {
    type EncryptionGroup = EdwardsBls;
    type EncryptionModelParameters = EdwardsParameters;
    type FiatShamirRng =
        FiatShamirAlgebraicSpongeRng<Self::InnerField, Self::OuterField, PoseidonSponge<Self::OuterField>>;
    type InnerSNARK = Groth16<InnerCurve, InnerCircuit<Components>, InnerCircuitVerifierInput<Components>>;
    type InnerSNARKGadget = Groth16VerifierGadget<InnerCurve, Self::OuterField, PairingGadget>;
    type MarlinMode = MarlinTestnet2Mode;
    type MerkleHashGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, Self::InnerField, EdwardsBlsGadget>;
    type MerkleParameters = CommitmentMerkleParameters;
    type NoopProgramSNARK = MarlinSNARK<
        Self::InnerField,
        Self::OuterField,
        Self::PolynomialCommitment,
        Self::FiatShamirRng,
        Self::MarlinMode,
        NoopCircuit<Self>,
        ProgramLocalData<Self>,
    >;
    type OuterSNARK = Groth16<OuterCurve, OuterCircuit<Components>, OuterCircuitVerifierInput<Components>>;
    type PolynomialCommitment = MarlinKZG10<InnerCurve>;
    type ProgramSNARKGadget = MarlinVerificationGadget<
        Self::InnerField,
        Self::OuterField,
        Self::PolynomialCommitment,
        MarlinKZG10Gadget<InnerCurve, OuterCurve, PairingGadget>,
    >;
}

pub type Testnet2DPC = DPC<Components>;
pub type Testnet2Transaction = Transaction<Components>;

pub type InnerCurve = Bls12_377;
pub type OuterCurve = BW6_761;

pub type LocalData = DPCLocalData<Components>;
pub type MerkleTreeCRH =
    BoweHopwoodPedersenCompressedCRH<EdwardsBls, MERKLE_TREE_CRH_NUM_WINDOWS, MERKLE_TREE_CRH_WINDOW_SIZE>;

// This is currently unused.
//
// use snarkvm_marlin::{FiatShamirAlgebraicSpongeRngVar, PoseidonSpongeVar};
//
// pub type FSG = FiatShamirAlgebraicSpongeRngVar<
//     Self::InnerField,
//     Self::OuterField,
//     PoseidonSponge<Self::OuterField>,
//     PoseidonSpongeVar<Self::OuterField>,
// >;
