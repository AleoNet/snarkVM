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
        BaseDPCComponents,
        LocalData as DPCLocalData,
        DPC,
    },
    traits::DPCComponents,
};
use snarkvm_algorithms::{
    commitment::{Blake2sCommitment, PedersenCompressedCommitment},
    crh::{BoweHopwoodPedersenCompressedCRH, PedersenSize},
    define_merkle_tree_parameters,
    encryption::GroupEncryption,
    prf::Blake2s,
    signature::SchnorrSignature,
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
    FiatShamirAlgebraicSpongeRngVar,
    PoseidonSponge,
    PoseidonSpongeVar,
};
use snarkvm_polycommit::marlin_pc::{marlin_kzg10::MarlinKZG10Gadget, MarlinKZG10};

use blake2::Blake2s as Blake2sHash;

pub const NUM_INPUT_RECORDS: usize = 2;
pub const NUM_OUTPUT_RECORDS: usize = 2;

// TODO (raychu86): Optimize windows.

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AccountWindow;
impl PedersenSize for AccountWindow {
    const NUM_WINDOWS: usize = 8;
    const WINDOW_SIZE: usize = 192;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EncryptedRecordWindow;

impl PedersenSize for EncryptedRecordWindow {
    const NUM_WINDOWS: usize = 48;
    const WINDOW_SIZE: usize = 44;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InnerSNARKVkHashWindow;

impl PedersenSize for InnerSNARKVkHashWindow {
    const NUM_WINDOWS: usize = 296;
    const WINDOW_SIZE: usize = 63;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalDataCommitmentWindow;

impl PedersenSize for LocalDataCommitmentWindow {
    const NUM_WINDOWS: usize = 8;
    const WINDOW_SIZE: usize = 129;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LocalDataCRHWindow;

impl PedersenSize for LocalDataCRHWindow {
    const NUM_WINDOWS: usize = 16;
    const WINDOW_SIZE: usize = 32;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProgramVkHashWindow;

impl PedersenSize for ProgramVkHashWindow {
    const NUM_WINDOWS: usize = 4096;
    const WINDOW_SIZE: usize = 80;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RecordWindow;
impl PedersenSize for RecordWindow {
    const NUM_WINDOWS: usize = 8;
    const WINDOW_SIZE: usize = 233;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SnNonceWindow;

impl PedersenSize for SnNonceWindow {
    const NUM_WINDOWS: usize = 32;
    const WINDOW_SIZE: usize = 63;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TwoToOneWindow;
impl PedersenSize for TwoToOneWindow {
    const NUM_WINDOWS: usize = 8;
    const WINDOW_SIZE: usize = 32;
}

define_merkle_tree_parameters!(CommitmentMerkleParameters, MerkleTreeCRH, 32);

pub struct Components;

impl DPCComponents for Components {
    type AccountCommitment = PedersenCompressedCommitment<EdwardsBls, AccountWindow>;
    type AccountCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;
    type AccountEncryption = GroupEncryption<EdwardsBls, EdwardsAffine, Blake2sHash>;
    type AccountEncryptionGadget = GroupEncryptionGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;
    type AccountSignature = SchnorrSignature<EdwardsAffine, Blake2sHash>;
    type AccountSignatureGadget = SchnorrPublicKeyRandomizationGadget<EdwardsAffine, InnerField, EdwardsBlsGadget>;
    type EncryptedRecordCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, EncryptedRecordWindow>;
    type EncryptedRecordCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;
    type InnerCircuitIDCRH = BoweHopwoodPedersenCompressedCRH<EdwardsSW, InnerSNARKVkHashWindow>;
    type InnerCircuitIDCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsSW, OuterField, EdwardsSWGadget>;
    type InnerField = InnerField;
    type LocalDataCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, LocalDataCRHWindow>;
    type LocalDataCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;
    type LocalDataCommitment = PedersenCompressedCommitment<EdwardsBls, LocalDataCommitmentWindow>;
    type LocalDataCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;
    type OuterField = OuterField;
    type PRF = Blake2s;
    type PRFGadget = Blake2sGadget;
    type ProgramVerificationKeyCRH = BoweHopwoodPedersenCompressedCRH<EdwardsSW, ProgramVkHashWindow>;
    type ProgramVerificationKeyCRHGadget =
        BoweHopwoodPedersenCompressedCRHGadget<EdwardsSW, OuterField, EdwardsSWGadget>;
    type ProgramVerificationKeyCommitment = Blake2sCommitment;
    type ProgramVerificationKeyCommitmentGadget = Blake2sCommitmentGadget;
    type RecordCommitment = PedersenCompressedCommitment<EdwardsBls, RecordWindow>;
    type RecordCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;
    type SerialNumberNonceCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, SnNonceWindow>;
    type SerialNumberNonceCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;

    const NUM_INPUT_RECORDS: usize = NUM_INPUT_RECORDS;
    const NUM_OUTPUT_RECORDS: usize = NUM_OUTPUT_RECORDS;
}

impl BaseDPCComponents for Components {
    type EncryptionGroup = EdwardsBls;
    type EncryptionModelParameters = EdwardsParameters;
    type FiatShamirRng = FiatShamirAlgebraicSpongeRng<InnerField, OuterField, PoseidonSponge<OuterField>>;
    type InnerSNARK = Groth16<InnerCurve, InnerCircuit<Components>, InnerCircuitVerifierInput<Components>>;
    type InnerSNARKGadget = Groth16VerifierGadget<InnerCurve, OuterField, PairingGadget>;
    type MarlinMode = MarlinTestnet2Mode;
    type MerkleHashGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls, InnerField, EdwardsBlsGadget>;
    type MerkleParameters = CommitmentMerkleParameters;
    type NoopProgramSNARK = MarlinSNARK<
        InnerField,
        OuterField,
        Self::PolynomialCommitment,
        Self::FiatShamirRng,
        Self::MarlinMode,
        NoopCircuit<Self>,
        ProgramLocalData<Self>,
    >;
    type OuterSNARK = Groth16<OuterCurve, OuterCircuit<Components>, OuterCircuitVerifierInput<Components>>;
    type PolynomialCommitment = MarlinKZG10<InnerCurve>;
    type ProgramSNARKGadget = MarlinVerificationGadget<InnerField, OuterField, Self::PolynomialCommitment, PCGadget>;
}

pub type InnerCurve = Bls12_377;
pub type OuterCurve = BW6_761;
pub type InnerField = Bls12_377Fr;
pub type OuterField = Bls12_377Fq;

pub type PCGadget = MarlinKZG10Gadget<InnerCurve, OuterCurve, PairingGadget>;

pub type FSG =
    FiatShamirAlgebraicSpongeRngVar<InnerField, OuterField, PoseidonSponge<OuterField>, PoseidonSpongeVar<OuterField>>;

pub type MerkleTreeCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls, TwoToOneWindow>;

pub type Tx = Transaction<Components>;

pub type InstantiatedDPC = DPC<Components>;
pub type LocalData = DPCLocalData<Components>;
