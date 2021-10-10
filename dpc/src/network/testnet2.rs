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
    account::ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT,
    posw::PoSW,
    Block,
    InnerPublicVariables,
    Network,
    OuterPublicVariables,
    PoSWScheme,
    Program,
    ProgramPublicVariables,
    ProgramScheme,
};
use snarkvm_algorithms::{
    commitment::BHPCommitment,
    crh::{PedersenCompressedCRH, BHPCRH},
    crypto_hash::PoseidonCryptoHash,
    encryption::ECIESPoseidonEncryption,
    merkle_tree::{MaskedMerkleTreeParameters, MerklePath, MerkleTreeParameters},
    prelude::*,
    prf::PoseidonPRF,
    signature::AleoSignatureScheme,
    snark::groth16::Groth16,
};
use snarkvm_curves::{
    bls12_377::Bls12_377,
    bw6_761::BW6_761,
    edwards_bls12::{
        EdwardsAffine as EdwardsBls12Affine,
        EdwardsParameters,
        EdwardsProjective as EdwardsBls12Projective,
    },
    edwards_bw6::EdwardsProjective as EdwardsBW6,
    traits::*,
};
use snarkvm_gadgets::{
    algorithms::{
        commitment::BHPCommitmentGadget,
        crh::{BHPCRHGadget, PedersenCompressedCRHGadget},
        crypto_hash::PoseidonCryptoHashGadget,
        encryption::ECIESPoseidonEncryptionGadget,
        prf::PoseidonPRFGadget,
        signature::AleoSignatureSchemeGadget,
        snark::Groth16VerifierGadget,
    },
    curves::{bls12_377::PairingGadget, edwards_bls12::EdwardsBls12Gadget, edwards_bw6::EdwardsBW6Gadget},
};
use snarkvm_marlin::{
    constraints::{snark::MarlinSNARK, verifier::MarlinVerificationGadget},
    marlin::MarlinTestnet2Mode,
    FiatShamirAlgebraicSpongeRng,
    PoseidonSponge,
};
use snarkvm_parameters::{testnet2::*, Genesis};
use snarkvm_polycommit::sonic_pc::{sonic_kzg10::SonicKZG10Gadget, SonicKZG10};
use snarkvm_utilities::{FromBytes, ToMinimalBits};

// TODO (howardwu): TEMPORARY - Resolve me.
use snarkvm_marlin::marlin::MarlinTestnet1Mode;

use once_cell::sync::OnceCell;
use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};
use std::{cell::RefCell, rc::Rc};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Testnet2;

// TODO (raychu86): Optimize each of the window sizes in the type declarations below.
#[rustfmt::skip]
impl Network for Testnet2 {
    const NETWORK_ID: u16 = 2u16;
    const NETWORK_NAME: &'static str = "testnet2";

    const NUM_INPUT_RECORDS: usize = 2;
    const NUM_OUTPUT_RECORDS: usize = 2;

    const MEMO_SIZE_IN_BYTES: usize = 64;

    const POSW_PROOF_SIZE_IN_BYTES: usize = 771;
    const POSW_NUM_LEAVES: usize = 8;
    const POSW_TREE_DEPTH: usize = 3;
    
    const ALEO_STARTING_SUPPLY_IN_CREDITS: i64 = 500_000;

    type InnerCurve = Bls12_377;
    type InnerScalarField = <Self::InnerCurve as PairingEngine>::Fr;
    
    type OuterCurve = BW6_761;
    type OuterBaseField = <Self::OuterCurve as PairingEngine>::Fq;
    type OuterScalarField = <Self::OuterCurve as PairingEngine>::Fr;

    type ProgramAffineCurve = EdwardsBls12Affine;
    type ProgramAffineCurveGadget = EdwardsBls12Gadget;
    type ProgramProjectiveCurve = EdwardsBls12Projective;
    type ProgramCurveParameters = EdwardsParameters;
    type ProgramBaseField = <Self::ProgramCurveParameters as ModelParameters>::BaseField;
    type ProgramScalarField = <Self::ProgramCurveParameters as ModelParameters>::ScalarField;

    type InnerSNARK = Groth16<Self::InnerCurve, InnerPublicVariables<Testnet2>>;
    type InnerSNARKGadget = Groth16VerifierGadget<Self::InnerCurve, PairingGadget>;

    type OuterSNARK = Groth16<Self::OuterCurve, OuterPublicVariables<Testnet2>>;

    type ProgramSNARK = MarlinSNARK<Self::InnerScalarField, Self::OuterScalarField, SonicKZG10<Self::InnerCurve>, FiatShamirAlgebraicSpongeRng<Self::InnerScalarField, Self::OuterScalarField, PoseidonSponge<Self::OuterScalarField>>, MarlinTestnet2Mode, ProgramPublicVariables<Self>>;
    type ProgramSNARKGadget = MarlinVerificationGadget<Self::InnerScalarField, Self::OuterScalarField, SonicKZG10<Self::InnerCurve>, SonicKZG10Gadget<Self::InnerCurve, Self::OuterCurve, PairingGadget>>;
    type ProgramProvingKey = <Self::ProgramSNARK as SNARK>::ProvingKey;
    type ProgramVerifyingKey = <Self::ProgramSNARK as SNARK>::VerifyingKey;
    type ProgramProof = <Self::ProgramSNARK as SNARK>::Proof;

    type PoswSNARK = MarlinSNARK<Self::InnerScalarField, Self::OuterScalarField, SonicKZG10<Self::InnerCurve>, FiatShamirAlgebraicSpongeRng<Self::InnerScalarField, Self::OuterScalarField, PoseidonSponge<Self::OuterScalarField>>, MarlinTestnet1Mode, Vec<Self::InnerScalarField>>;
    type PoSWProof = <Self::PoswSNARK as SNARK>::Proof;

    type AccountEncryptionScheme = ECIESPoseidonEncryption<Self::ProgramCurveParameters>;
    type AccountEncryptionGadget = ECIESPoseidonEncryptionGadget<Self::ProgramCurveParameters, Self::InnerScalarField>;

    type AccountPRF = PoseidonPRF<Self::ProgramScalarField, 4, false>;
    type AccountSeed = <Self::AccountPRF as PRF>::Seed;
    
    type AccountSignatureScheme = AleoSignatureScheme<Self::ProgramCurveParameters>;
    type AccountSignatureGadget = AleoSignatureSchemeGadget<Self::ProgramCurveParameters, Self::InnerScalarField>;
    type AccountSignaturePublicKey = <Self::AccountSignatureScheme as SignatureScheme>::PublicKey;
    type AccountSignature = <Self::AccountSignatureScheme as SignatureScheme>::Signature;

    type BlockHashCRH = BHPCRH<Self::ProgramProjectiveCurve, 16, 32>;
    type BlockHashCRHGadget = BHPCRHGadget<Self::ProgramProjectiveCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 16, 32>;
    type BlockHash = <Self::BlockHashCRH as CRH>::Output;

    type BlockHeaderTreeCRH = PedersenCompressedCRH<Self::ProgramProjectiveCurve, 4, 128>;
    type BlockHeaderTreeCRHGadget = PedersenCompressedCRHGadget<Self::ProgramProjectiveCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 4, 128>;
    type BlockHeaderTreeParameters = MaskedMerkleTreeParameters<Self::BlockHeaderTreeCRH, 3>;
    type BlockHeaderRoot = <Self::BlockHeaderTreeCRH as CRH>::Output;

    type CiphertextIDCRH = BHPCRH<Self::ProgramProjectiveCurve, 41, 63>;
    type CiphertextIDCRHGadget = BHPCRHGadget<Self::ProgramProjectiveCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 41, 63>;
    type CiphertextID = <Self::CiphertextIDCRH as CRH>::Output;

    type CommitmentScheme = BHPCommitment<Self::ProgramProjectiveCurve, 34, 63>;
    type CommitmentGadget = BHPCommitmentGadget<Self::ProgramProjectiveCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 34, 63>;
    type Commitment = <Self::CommitmentScheme as CommitmentScheme>::Output;

    type CommitmentsTreeCRH = BHPCRH<Self::ProgramProjectiveCurve, 16, 32>;
    type CommitmentsTreeCRHGadget = BHPCRHGadget<Self::ProgramProjectiveCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 16, 32>;
    type CommitmentsTreeParameters = MerkleTreeParameters<Self::CommitmentsTreeCRH, 42>;
    type CommitmentsRoot = <Self::CommitmentsTreeCRH as CRH>::Output;

    type FunctionIDCRH = BHPCRH<EdwardsBW6, 237, 16>;
    type FunctionIDCRHGadget = BHPCRHGadget<EdwardsBW6, Self::OuterScalarField, EdwardsBW6Gadget, 237, 16>;
    type FunctionID = <Self::FunctionIDCRH as CRH>::Output;
    
    type FunctionInputsCRH = PoseidonCryptoHash::<Self::InnerScalarField, 4, false>;
    type FunctionInputsCRHGadget = PoseidonCryptoHashGadget<Self::InnerScalarField, 4, false>;
    type FunctionInputsDigest= <Self::FunctionInputsCRH as CryptoHash>::Output;

    type InnerCircuitIDCRH = BHPCRH<EdwardsBW6, 68, 63>;
    type InnerCircuitIDCRHGadget = BHPCRHGadget<EdwardsBW6, Self::OuterScalarField, EdwardsBW6Gadget, 68, 63>;
    type InnerCircuitID = <Self::InnerCircuitIDCRH as CRH>::Output;

    type LocalCommitmentsTreeCRH = BHPCRH<Self::ProgramProjectiveCurve, 16, 32>;
    type LocalCommitmentsTreeCRHGadget = BHPCRHGadget<Self::ProgramProjectiveCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 16, 32>;
    type LocalCommitmentsTreeParameters = MerkleTreeParameters<Self::LocalCommitmentsTreeCRH, 8>;
    type LocalCommitmentsRoot = <Self::LocalCommitmentsTreeCRH as CRH>::Output;
    
    type PoSWMaskPRF = PoseidonPRF<Self::InnerScalarField, 4, false>;
    type PoSWMaskPRFGadget = PoseidonPRFGadget<Self::InnerScalarField, 4, false>;
    type PoSW = PoSW<Self>;

    type ProgramFunctionsTreeCRH = BHPCRH<EdwardsBW6, 16, 48>;
    type ProgramFunctionsTreeCRHGadget = BHPCRHGadget<EdwardsBW6, Self::OuterScalarField, EdwardsBW6Gadget, 16, 48>;
    type ProgramFunctionsTreeParameters = MerkleTreeParameters<Self::ProgramFunctionsTreeCRH, 8>;
    type ProgramID = <Self::ProgramFunctionsTreeCRH as CRH>::Output;
    
    type SerialNumberPRF = PoseidonPRF<Self::InnerScalarField, 4, false>;
    type SerialNumberPRFGadget = PoseidonPRFGadget<Self::InnerScalarField, 4, false>;
    type SerialNumber = <Self::SerialNumberPRF as PRF>::Output;

    type SerialNumbersTreeCRH = BHPCRH<Self::ProgramProjectiveCurve, 16, 32>;
    type SerialNumbersTreeParameters = MerkleTreeParameters<Self::SerialNumbersTreeCRH, 42>;
    type SerialNumbersRoot = <Self::SerialNumbersTreeCRH as CRH>::Output;

    type TransactionIDCRH = BHPCRH<Self::ProgramProjectiveCurve, 66, 63>;
    type TransactionID = <Self::TransactionIDCRH as CRH>::Output;

    type TransactionsTreeCRH = BHPCRH<Self::ProgramProjectiveCurve, 16, 32>;
    type TransactionsTreeParameters = MerkleTreeParameters<Self::TransactionsTreeCRH, 16>;
    type TransactionsRoot = <Self::TransactionsTreeCRH as CRH>::Output;

    type TransitionIDCRH = BHPCRH<Self::ProgramProjectiveCurve, 34, 63>;
    type TransitionIDCRHGadget = BHPCRHGadget<Self::ProgramProjectiveCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 34, 63>;
    type TransitionID = <Self::TransitionIDCRH as CRH>::Output;

    dpc_setup!{Testnet2, account_encryption_scheme, AccountEncryptionScheme, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT}
    dpc_setup!{Testnet2, account_signature_scheme, AccountSignatureScheme, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT}
    dpc_setup!{Testnet2, block_hash_crh, BlockHashCRH, "AleoBlockHashCRH0"}
    dpc_setup!{Testnet2, block_header_tree_parameters, BlockHeaderTreeParameters, "AleoBlockHeaderTreeCRH0"}
    dpc_setup!{Testnet2, ciphertext_id_crh, CiphertextIDCRH, "AleoCiphertextIDCRH0"}
    dpc_setup!{Testnet2, commitment_scheme, CommitmentScheme, "AleoCommitmentScheme0"}
    dpc_setup!{Testnet2, commitments_tree_parameters, CommitmentsTreeParameters, "AleoCommitmentsTreeCRH0"}
    dpc_setup!{Testnet2, function_id_crh, FunctionIDCRH, "AleoFunctionIDCRH0"}
    dpc_setup!{Testnet2, inner_circuit_id_crh, InnerCircuitIDCRH, "AleoInnerCircuitIDCRH0"}
    dpc_setup!{Testnet2, local_commitments_tree_parameters, LocalCommitmentsTreeParameters, "AleoLocalCommitmentsTreeCRH0"}
    dpc_setup!{Testnet2, program_functions_tree_parameters, ProgramFunctionsTreeParameters, "AleoProgramFunctionsTreeCRH0"}
    dpc_setup!{Testnet2, serial_numbers_tree_parameters, SerialNumbersTreeParameters, "AleoSerialNumbersTreeCRH0"}
    dpc_setup!{Testnet2, transaction_id_crh, TransactionIDCRH, "AleoTransactionIDCRH0"}
    dpc_setup!{Testnet2, transactions_tree_parameters, TransactionsTreeParameters, "AleoTransactionsTreeCRH0"}
    dpc_setup!{Testnet2, transition_id_crh, TransitionIDCRH, "AleoTransitionIDCRH0"}

    dpc_snark_setup!{Testnet2, inner_proving_key, InnerSNARK, ProvingKey, InnerProvingKeyBytes, "inner circuit proving key"}
    dpc_snark_setup!{Testnet2, inner_verifying_key, InnerSNARK, VerifyingKey, InnerVerifyingKeyBytes, "inner circuit verifying key"}

    dpc_snark_setup!{Testnet2, outer_proving_key, OuterSNARK, ProvingKey, OuterProvingKeyBytes, "outer circuit proving key"}
    dpc_snark_setup!{Testnet2, outer_verifying_key, OuterSNARK, VerifyingKey, OuterVerifyingKeyBytes, "outer circuit verifying key"}

    dpc_snark_setup!{Testnet2, noop_circuit_proving_key, ProgramSNARK, ProvingKey, NoopProvingKeyBytes, "noop circuit proving key"}
    dpc_snark_setup!{Testnet2, noop_circuit_verifying_key, ProgramSNARK, VerifyingKey, NoopVerifyingKeyBytes, "noop circuit verifying key"}

    fn inner_circuit_id() -> &'static Self::InnerCircuitID {
        static INNER_CIRCUIT_ID: OnceCell<<Testnet2 as Network>::InnerCircuitID> = OnceCell::new();
        INNER_CIRCUIT_ID.get_or_init(|| Self::inner_circuit_id_crh()
            .hash_bits(&Self::inner_verifying_key().to_minimal_bits())
            .expect("Failed to hash inner circuit verifying key elements"))
    }
    
    fn noop_program() -> &'static Program<Self> {
        static NOOP_PROGRAM: OnceCell<Program<Testnet2>> = OnceCell::new();
        NOOP_PROGRAM.get_or_init(|| Program::<Testnet2>::new_noop().expect("Failed to fetch the noop program"))
    }

    fn noop_program_id() -> &'static Self::ProgramID {
        static NOOP_PROGRAM_ID: OnceCell<<Testnet2 as Network>::ProgramID> = OnceCell::new();
        NOOP_PROGRAM_ID.get_or_init(|| Testnet2::noop_program().program_id())
    }

    fn noop_program_path() -> &'static MerklePath<Self::ProgramFunctionsTreeParameters> {
        static NOOP_PROGRAM_PATH: OnceCell<MerklePath<<Testnet2 as Network>::ProgramFunctionsTreeParameters>> = OnceCell::new();
        NOOP_PROGRAM_PATH.get_or_init(|| Self::noop_program().to_program_path(Self::noop_function_id()).expect("Failed to fetch the noop program path"))
    }
    
    fn noop_function_id() -> &'static Self::FunctionID {
        static NOOP_FUNCTION_ID: OnceCell<<Testnet2 as Network>::FunctionID> = OnceCell::new();
        NOOP_FUNCTION_ID.get_or_init(|| Self::function_id(Self::noop_circuit_verifying_key()).expect("Failed to hash noop circuit verifying key"))
    }

    fn posw() -> &'static Self::PoSW {
        static POSW: OnceCell<<Testnet2 as Network>::PoSW> = OnceCell::new();
        POSW.get_or_init(|| <Self::PoSW as PoSWScheme<Self>>::load(true).expect("Failed to load PoSW"))
    }
    
    fn genesis_block() -> &'static Block<Self> {
        static BLOCK: OnceCell<Block<Testnet2>> = OnceCell::new();
        BLOCK.get_or_init(|| FromBytes::read_le(&GenesisBlock::load_bytes()[..]).expect("Failed to load genesis block"))
    }
    
    /// Returns the program SRS for Aleo applications.
    fn program_srs<R: Rng + CryptoRng>(_rng: &mut R) -> Rc<RefCell<SRS<R, <Self::ProgramSNARK as SNARK>::UniversalSetupParameters>>> {
        static UNIVERSAL_SRS: OnceCell<<<Testnet2 as Network>::ProgramSNARK as SNARK>::UniversalSetupParameters> = OnceCell::new();
        let universal_srs = UNIVERSAL_SRS.get_or_init(|| <Self::ProgramSNARK as SNARK>::UniversalSetupParameters::from_bytes_le(
            &UniversalSRSBytes::load_bytes().expect("Failed to load universal SRS bytes"),
        ).unwrap());
        Rc::new(RefCell::new(SRS::<_, _>::Universal(universal_srs)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_network_name_sanity_check() {
        assert_eq!(Testnet2::NETWORK_NAME, "testnet2");
    }

    #[test]
    fn test_inner_circuit_sanity_check() {
        // Verify the inner circuit verifying key matches the one derived from the inner circuit proving key.
        assert_eq!(
            Testnet2::inner_verifying_key(),
            &Testnet2::inner_proving_key().vk,
            "The inner circuit verifying key does not correspond to the inner circuit proving key"
        );
    }

    #[test]
    fn test_inner_circuit_id_derivation() {
        // Verify the inner circuit ID matches the one derived from the inner circuit verifying key.
        assert_eq!(
            Testnet2::inner_circuit_id(),
            &Testnet2::inner_circuit_id_crh()
                .hash_bits(&Testnet2::inner_verifying_key().to_minimal_bits())
                .expect("Failed to hash inner circuit ID"),
            "The inner circuit ID does not correspond to the inner circuit verifying key"
        );
    }

    #[test]
    fn test_outer_circuit_sanity_check() {
        // Verify the outer circuit verifying key matches the one derived from the outer circuit proving key.
        assert_eq!(
            Testnet2::outer_verifying_key(),
            &Testnet2::outer_proving_key().vk,
            "The outer circuit verifying key does not correspond to the outer circuit proving key"
        );
    }

    #[test]
    fn test_posw_tree_sanity_check() {
        // Verify the PoSW tree depth matches the declared depth.
        assert_eq!(Testnet2::POSW_TREE_DEPTH, 3); // Testnet2 has a tree depth of 3.
        assert_eq!(
            Testnet2::POSW_TREE_DEPTH,
            <<Testnet2 as Network>::BlockHeaderTreeParameters as MerkleParameters>::DEPTH
        );

        // Verify the number of leaves corresponds to the correct tree depth.
        let num_leaves = 2u32.pow(Testnet2::POSW_TREE_DEPTH as u32) as usize;
        assert_eq!(Testnet2::POSW_NUM_LEAVES, num_leaves);
    }
}
