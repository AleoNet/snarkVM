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
    DPCComponents,
    Network,
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
    bls12_377::Bls12_377,
    bw6_761::BW6_761,
    edwards_bls12::{EdwardsAffine, EdwardsParameters, EdwardsProjective as EdwardsBls12},
    edwards_bw6::EdwardsProjective as EdwardsBW6,
    PairingEngine,
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
    curves::{bls12_377::PairingGadget, edwards_bls12::EdwardsBls12Gadget, edwards_bw6::EdwardsBW6Gadget},
    fields::FpGadget,
};
use snarkvm_marlin::{
    constraints::{snark::MarlinSNARK, verifier::MarlinVerificationGadget},
    marlin::MarlinTestnet2Mode,
    FiatShamirAlgebraicSpongeRng,
    PoseidonSponge,
};
use snarkvm_polycommit::marlin_pc::{marlin_kzg10::MarlinKZG10Gadget, MarlinKZG10};

use blake2::Blake2s as Blake2sHash;

pub type Testnet2DPC = DPC<Components>;
pub type Testnet2Transaction = Transaction<Components>;

pub type LocalData = DPCLocalData<Components>;
pub type MerkleTreeCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 8, 32>;

define_merkle_tree_parameters!(CommitmentMerkleParameters, MerkleTreeCRH, 32);

pub struct Components;

// TODO (raychu86): Optimize each of the window sizes in the type declarations below.
#[rustfmt::skip]
impl DPCComponents for Components {
    const NETWORK_ID: u8 = Network::Testnet2.id();

    const NUM_INPUT_RECORDS: usize = 2;
    const NUM_OUTPUT_RECORDS: usize = 2;
    
    type InnerCurve = Bls12_377;
    type OuterCurve = BW6_761;

    type InnerScalarField = <Self::InnerCurve as PairingEngine>::Fr;
    type OuterScalarField = <Self::OuterCurve as PairingEngine>::Fr;
    
    type AccountCommitment = PedersenCompressedCommitment<EdwardsBls12, 8, 192>;
    type AccountCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
    
    type AccountEncryption = GroupEncryption<EdwardsBls12, EdwardsAffine, Blake2sHash>;
    type AccountEncryptionGadget = GroupEncryptionGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;

    type AccountSignature = Schnorr<EdwardsAffine, Blake2sHash>;
    type AccountSignatureGadget = SchnorrPublicKeyRandomizationGadget<EdwardsAffine, Self::InnerScalarField, EdwardsBls12Gadget, FpGadget<Self::InnerScalarField>>;
    
    type EncryptedRecordCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 48, 44>;
    type EncryptedRecordCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
    
    type InnerCircuitIDCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBW6, 296, 63>;
    type InnerCircuitIDCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBW6, Self::OuterScalarField, EdwardsBW6Gadget>;
    
    type LocalDataCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 16, 32>;
    type LocalDataCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
    
    type LocalDataCommitment = PedersenCompressedCommitment<EdwardsBls12, 8, 129>;
    type LocalDataCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
    
    type PRF = Blake2s;
    type PRFGadget = Blake2sGadget;
    
    type ProgramVerificationKeyCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBW6, 4096, 80>;
    type ProgramVerificationKeyCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBW6, Self::OuterScalarField, EdwardsBW6Gadget>;
    
    type ProgramVerificationKeyCommitment = Blake2sCommitment;
    type ProgramVerificationKeyCommitmentGadget = Blake2sCommitmentGadget;
    
    type RecordCommitment = PedersenCompressedCommitment<EdwardsBls12, 8, 233>;
    type RecordCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
    
    type SerialNumberNonceCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 32, 63>;
    type SerialNumberNonceCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
}

impl Testnet2Components for Components {
    type EncryptionGroup = EdwardsBls12;
    type EncryptionGroupGadget = EdwardsBls12Gadget;
    type EncryptionModelParameters = EdwardsParameters;
    type FiatShamirRng = FiatShamirAlgebraicSpongeRng<
        Self::InnerScalarField,
        Self::OuterScalarField,
        PoseidonSponge<Self::OuterScalarField>,
    >;
    type InnerSNARK = Groth16<Self::InnerCurve, InnerCircuit<Components>, InnerCircuitVerifierInput<Components>>;
    type InnerSNARKGadget = Groth16VerifierGadget<Self::InnerCurve, Self::OuterScalarField, PairingGadget>;
    type MarlinMode = MarlinTestnet2Mode;
    type MerkleHashGadget =
        BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
    type MerkleParameters = CommitmentMerkleParameters;
    type NoopProgramSNARK = MarlinSNARK<
        Self::InnerScalarField,
        Self::OuterScalarField,
        Self::PolynomialCommitment,
        Self::FiatShamirRng,
        Self::MarlinMode,
        NoopCircuit<Self>,
        ProgramLocalData<Self>,
    >;
    type NoopProgramSNARKGadget = MarlinVerificationGadget<
        Self::InnerScalarField,
        Self::OuterScalarField,
        Self::PolynomialCommitment,
        MarlinKZG10Gadget<Self::InnerCurve, Self::OuterCurve, PairingGadget>,
    >;
    type OuterSNARK = Groth16<Self::OuterCurve, OuterCircuit<Components>, OuterCircuitVerifierInput<Components>>;
    type PolynomialCommitment = MarlinKZG10<Self::InnerCurve>;
}

// This is currently unused.
//
// use snarkvm_marlin::{FiatShamirAlgebraicSpongeRngVar, PoseidonSpongeVar};
//
// pub type FSG = FiatShamirAlgebraicSpongeRngVar<
//     Self::InnerScalarField,
//     Self::OuterScalarField,
//     PoseidonSponge<Self::OuterScalarField>,
//     PoseidonSpongeVar<Self::OuterScalarField>,
// >;
