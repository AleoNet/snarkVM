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
    testnet1::{
        inner_circuit::InnerCircuit,
        inner_circuit_verifier_input::InnerCircuitVerifierInput,
        outer_circuit::OuterCircuit,
        outer_circuit_verifier_input::OuterCircuitVerifierInput,
        program::{NoopCircuit, ProgramLocalData},
        transaction::Transaction,
        Testnet1Components,
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
    snark::{gm17::GM17, groth16::Groth16},
};
use snarkvm_curves::{
    bls12_377::Bls12_377,
    bw6_761::BW6_761,
    edwards_bls12::{EdwardsParameters, EdwardsProjective as EdwardsBls12},
    edwards_bw6::EdwardsProjective as EdwardsBW6,
    PairingEngine,
};
use snarkvm_gadgets::{
    algorithms::{
        commitment::{Blake2sCommitmentGadget, PedersenCompressedCommitmentGadget},
        crh::BoweHopwoodPedersenCompressedCRHGadget,
        encryption::GroupEncryptionGadget,
        prf::Blake2sGadget,
        signature::SchnorrGadget,
        snark::{GM17VerifierGadget, Groth16VerifierGadget},
    },
    curves::{bls12_377::PairingGadget, edwards_bls12::EdwardsBls12Gadget, edwards_bw6::EdwardsBW6Gadget},
};

pub type Testnet1DPC = DPC<Components>;
pub type Testnet1Transaction = Transaction<Components>;

pub type MerkleTreeCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 8, 32>;

define_merkle_tree_parameters!(CommitmentMerkleParameters, MerkleTreeCRH, 32);

pub struct Components;

#[rustfmt::skip]
impl DPCComponents for Components {
    const NETWORK_ID: u8 = Network::Testnet1.id();
    
    const NUM_INPUT_RECORDS: usize = 2;
    const NUM_OUTPUT_RECORDS: usize = 2;

    type InnerCurve = Bls12_377;
    type OuterCurve = BW6_761;

    type InnerScalarField = <Self::InnerCurve as PairingEngine>::Fr;
    type OuterScalarField = <Self::OuterCurve as PairingEngine>::Fr;
    
    type AccountCommitment = PedersenCompressedCommitment<EdwardsBls12, 8, 192>;
    type AccountCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 8, 192>;
    
    type AccountEncryption = GroupEncryption<EdwardsBls12, EdwardsBls12>;
    type AccountEncryptionGadget = GroupEncryptionGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;

    type AccountSignature = Schnorr<EdwardsBls12>;
    type AccountSignatureGadget = SchnorrGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget>;
    
    type EncryptedRecordCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 48, 44>;
    type EncryptedRecordCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 48, 44>;
    
    type InnerCircuitIDCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBW6, 296, 63>;
    type InnerCircuitIDCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBW6, Self::OuterScalarField, EdwardsBW6Gadget, 296, 63>;
    
    type LocalDataCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 16, 32>;
    type LocalDataCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 16, 32>;
    
    type LocalDataCommitment = PedersenCompressedCommitment<EdwardsBls12, 8, 129>;
    type LocalDataCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 8, 129>;

    type PRF = Blake2s;
    type PRFGadget = Blake2sGadget;
    
    type ProgramVerificationKeyCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBW6, 144, 63>;
    type ProgramVerificationKeyCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBW6, Self::OuterScalarField, EdwardsBW6Gadget, 144, 63>;
    
    type ProgramVerificationKeyCommitment = Blake2sCommitment;
    type ProgramVerificationKeyCommitmentGadget = Blake2sCommitmentGadget;
    
    type RecordCommitment = PedersenCompressedCommitment<EdwardsBls12, 8, 233>;
    type RecordCommitmentGadget = PedersenCompressedCommitmentGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 8, 233>;
    
    type SerialNumberNonceCRH = BoweHopwoodPedersenCompressedCRH<EdwardsBls12, 32, 63>;
    type SerialNumberNonceCRHGadget = BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 32, 63>;
}

impl Testnet1Components for Components {
    type EncryptionGroup = EdwardsBls12;
    type EncryptionParameters = EdwardsParameters;
    type InnerSNARK = Groth16<Self::InnerCurve, InnerCircuit<Components>, InnerCircuitVerifierInput<Components>>;
    type InnerSNARKGadget = Groth16VerifierGadget<Self::InnerCurve, Self::OuterScalarField, PairingGadget>;
    type MerkleHashGadget =
        BoweHopwoodPedersenCompressedCRHGadget<EdwardsBls12, Self::InnerScalarField, EdwardsBls12Gadget, 8, 32>;
    type MerkleParameters = CommitmentMerkleParameters;
    type NoopProgramSNARK = GM17<Self::InnerCurve, NoopCircuit<Self>, ProgramLocalData<Self>>;
    type NoopProgramSNARKGadget = GM17VerifierGadget<Self::InnerCurve, Self::OuterScalarField, PairingGadget>;
    type OuterSNARK = Groth16<Self::OuterCurve, OuterCircuit<Components>, OuterCircuitVerifierInput<Components>>;
}
