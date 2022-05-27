// Copyright (C) 2019-2022 Aleo Systems Inc.
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
    AleoLocator,
    AleoObject,
    Block,
    Ciphertext,
    InputPublicVariables,
    Network,
    OutputPublicVariables,
    PoSWScheme,
    ProgramPublicVariables,
    ValueBalanceCommitment,
};
use snarkvm_algorithms::{
    commitment::PedersenCommitment,
    crh::{PedersenCompressedCRH, PoseidonCRH, BHPCRH},
    crypto_hash::PoseidonSponge,
    encryption::ECIESPoseidonEncryption,
    merkle_tree::{MaskedMerkleTreeParameters, MerkleTreeParameters},
    prelude::*,
    prf::PoseidonPRF,
    signature::AleoSignatureScheme,
    snark::marlin::{
        FiatShamirAlgebraicSpongeRng,
        FiatShamirChaChaRng,
        MarlinHidingMode,
        MarlinNonHidingMode,
        MarlinSNARK,
    },
};
use snarkvm_curves::{
    bls12_377::Bls12_377,
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
        commitment::PedersenCommitmentGadget,
        crh::{BHPCRHGadget, PedersenCompressedCRHGadget, PoseidonCRHGadget},
        encryption::ECIESPoseidonEncryptionGadget,
        prf::PoseidonPRFGadget,
        signature::AleoSignatureSchemeGadget,
    },
    curves::edwards_bls12::EdwardsBls12Gadget,
};
use snarkvm_parameters::{testnet2::*, Genesis};
use snarkvm_utilities::{FromBytes, ToMinimalBits};

use blake2::Blake2s256;
use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Testnet2;

// TODO (raychu86): Optimize each of the window sizes in the type declarations below.
#[rustfmt::skip]
impl Network for Testnet2 {
    const NETWORK_ID: u16 = 2u16;
    const NETWORK_NAME: &'static str = "testnet2";

    const NUM_TRANSITIONS: u8 = u8::pow(2, Self::TRANSACTION_TREE_DEPTH as u32);
    const NUM_EVENTS: u16 = 2;

    const NUM_INPUTS: u16 = 16;
    const NUM_OUTPUTS: u16 = 16;

    const BLOCK_HASH_PREFIX: u16 = hrp2!("ab");
    const LEDGER_ROOT_PREFIX: u16 = hrp2!("al");
    const PROGRAM_ID_PREFIX: u16 = hrp2!("ap");
    const TRANSITION_ID_PREFIX: u16 = hrp2!("as");
    const TRANSACTION_ID_PREFIX: u16 = hrp2!("at");

    const COMMITMENT_PREFIX: u16 = hrp2!("cm");
    const FUNCTION_INPUTS_HASH_PREFIX: u16 = hrp2!("fi");
    const FUNCTION_ID_PREFIX: u16 = hrp2!("fn");
    const HEADER_NONCE_PREFIX: u16 = hrp2!("hn");
    const HEADER_ROOT_PREFIX: u16 = hrp2!("hr");
    const HEADER_TRANSACTIONS_ROOT_PREFIX: u16 = hrp2!("ht");
    const RECORD_RANDOMIZER_PREFIX: u16 = hrp2!("rr");
    const RECORD_VIEW_KEY_COMMITMENT_PREFIX: u16 = hrp2!("rc");
    const SERIAL_NUMBER_PREFIX: u16 = hrp2!("sn");

    const HEADER_PROOF_PREFIX: u32 = hrp4!("hzkp");
    const PROGRAM_PROOF_PREFIX: u32 = hrp4!("pzkp");
    const RECORD_CIPHERTEXT_PREFIX: u32 = hrp4!("recd");
    const RECORD_VIEW_KEY_PREFIX: u32 = hrp4!("rcvk");
    const SIGNATURE_PREFIX: u32 = hrp4!("sign");
    const VALUE_COMMITMENT_PREFIX: u32 = hrp4!("valc");
    const VALUE_BALANCE_COMMITMENT_PREFIX: u32 = hrp4!("vbco");

    const INPUT_CIRCUIT_ID_PREFIX: u16 = hrp2!("ic");
    const OUTPUT_CIRCUIT_ID_PREFIX: u16 = hrp2!("oc");
    
    const INPUT_PROOF_PREFIX: u32 = hrp4!("izkp");
    const OUTPUT_PROOF_PREFIX: u32 = hrp4!("ozkp");

    const ADDRESS_SIZE_IN_BYTES: usize = 32;
    const HEADER_SIZE_IN_BYTES: usize = 936;
    const HEADER_PROOF_SIZE_IN_BYTES: usize = 804;
    const PROGRAM_PROOF_SIZE_IN_BYTES: usize = 971;
    const PROGRAM_ID_SIZE_IN_BYTES: usize = 32;
    const RECORD_CIPHERTEXT_SIZE_IN_BYTES: usize = 292;
    const RECORD_PAYLOAD_SIZE_IN_BYTES: usize = 128;
    const RECORD_VIEW_KEY_SIZE_IN_BYTES: usize = 32;
    const SIGNATURE_SIZE_IN_BYTES: usize = 128;
    const VALUE_COMMITMENT_SIZE_IN_BYTES: usize = 64;
    const VALUE_BALANCE_COMMITMENT_SIZE_IN_BYTES: usize = 96;

    const INPUT_PROOF_SIZE_IN_BYTES: usize = 884;
    const OUTPUT_PROOF_SIZE_IN_BYTES: usize = 884;
    
    const HEADER_TRANSACTIONS_TREE_DEPTH: usize = 15;
    const HEADER_TREE_DEPTH: usize = 2;
    const LEDGER_TREE_DEPTH: usize = 32;
    const PROGRAM_TREE_DEPTH: usize = 8;
    const TRANSITION_TREE_DEPTH: usize = 5;
    const TRANSACTION_TREE_DEPTH: usize = 5;

    const ALEO_BLOCK_TIME_IN_SECS: i64 = 20i64;
    const ALEO_STARTING_SUPPLY_IN_CREDITS: i64 = 1_000_000_000;
    const ALEO_FUTURE_TIME_LIMIT_IN_SECS: i64 = 90;
    const ALEO_MAXIMUM_FORK_DEPTH: u32 = 4096;

    type InnerCurve = Bls12_377;
    type InnerScalarField = <Self::InnerCurve as PairingEngine>::Fr;
    type InnerBaseField = <Self::InnerCurve as PairingEngine>::Fq;

    type ProgramAffineCurve = EdwardsBls12Affine;
    type ProgramAffineCurveGadget = EdwardsBls12Gadget;
    type ProgramProjectiveCurve = EdwardsBls12Projective;
    type ProgramCurveParameters = EdwardsParameters;
    type ProgramScalarField = <Self::ProgramCurveParameters as ModelParameters>::ScalarField;

    type InputSNARK = MarlinSNARK<Self::InnerCurve, FiatShamirAlgebraicSpongeRng<Self::InnerScalarField, Self::InnerBaseField, PoseidonSponge<Self::InnerBaseField, 6, 1>>, MarlinHidingMode, InputPublicVariables<Self>>;
    type InputProof = AleoObject<<Self::InputSNARK as SNARK>::Proof, { Self::INPUT_PROOF_PREFIX }, { Self::INPUT_PROOF_SIZE_IN_BYTES }>;

    type OutputSNARK = MarlinSNARK<Self::InnerCurve, FiatShamirAlgebraicSpongeRng<Self::InnerScalarField, Self::InnerBaseField, PoseidonSponge<Self::InnerBaseField, 6, 1>>, MarlinHidingMode, OutputPublicVariables<Self>>;
    type OutputProof = AleoObject<<Self::OutputSNARK as SNARK>::Proof, { Self::OUTPUT_PROOF_PREFIX }, { Self::OUTPUT_PROOF_SIZE_IN_BYTES }>;

    type ProgramSNARK = MarlinSNARK<Self::InnerCurve, FiatShamirAlgebraicSpongeRng<Self::InnerScalarField, Self::InnerBaseField, PoseidonSponge<Self::InnerBaseField, 6, 1>>, MarlinHidingMode, ProgramPublicVariables<Self>>;
    type ProgramProvingKey = <Self::ProgramSNARK as SNARK>::ProvingKey;
    type ProgramVerifyingKey = <Self::ProgramSNARK as SNARK>::VerifyingKey;
    type ProgramProof = AleoObject<<Self::ProgramSNARK as SNARK>::Proof, { Self::PROGRAM_PROOF_PREFIX }, { Self::PROGRAM_PROOF_SIZE_IN_BYTES }>;

    type PoSWSNARK = MarlinSNARK<Self::InnerCurve, FiatShamirChaChaRng<Self::InnerScalarField, Self::InnerBaseField, Blake2s256>, MarlinNonHidingMode, Vec<Self::InnerScalarField>>;
    type PoSWProof = AleoObject<<Self::PoSWSNARK as SNARK>::Proof, { Self::HEADER_PROOF_PREFIX }, { Self::HEADER_PROOF_SIZE_IN_BYTES }>;
    type PoSW = PoSW<Self>;

    type AccountEncryptionScheme = ECIESPoseidonEncryption<Self::ProgramCurveParameters>;
    type AccountEncryptionGadget = ECIESPoseidonEncryptionGadget<Self::ProgramCurveParameters, Self::InnerScalarField>;

    type AccountSeedPRF = PoseidonPRF<Self::ProgramScalarField, 4>;
    type AccountSeed = <Self::AccountSeedPRF as PRF>::Seed;
    
    type AccountSignatureScheme = AleoSignatureScheme<Self::ProgramCurveParameters>;
    type AccountSignatureGadget = AleoSignatureSchemeGadget<Self::ProgramCurveParameters, Self::InnerScalarField>;
    type AccountSignaturePublicKey = <Self::AccountSignatureScheme as SignatureScheme>::PublicKey;
    type AccountSignature = AleoObject<<Self::AccountSignatureScheme as SignatureScheme>::Signature, { Self::SIGNATURE_PREFIX }, { Self::SIGNATURE_SIZE_IN_BYTES }>;

    type BlockHashCRH = BHPCRH<Self::ProgramProjectiveCurve, 3, 57>;
    type BlockHashCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 3, 57>;
    type BlockHash = AleoLocator<<Self::BlockHashCRH as CRH>::Output, { Self::BLOCK_HASH_PREFIX }>;

    type BlockHeaderRootCRH = PedersenCompressedCRH<Self::ProgramProjectiveCurve, 8, 36>;
    type BlockHeaderRootCRHGadget = PedersenCompressedCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 8, 36>;
    type BlockHeaderRootTwoToOneCRH = PedersenCompressedCRH<Self::ProgramProjectiveCurve, 4, 128>;
    type BlockHeaderRootTwoToOneCRHGadget = PedersenCompressedCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 4, 128>;
    type BlockHeaderRootParameters = MaskedMerkleTreeParameters<Self::BlockHeaderRootCRH, Self::BlockHeaderRootTwoToOneCRH, { Self::HEADER_TREE_DEPTH }>;
    type BlockHeaderRoot = AleoLocator<<Self::BlockHeaderRootCRH as CRH>::Output, { Self::HEADER_ROOT_PREFIX }>;

    type CommitmentScheme = BHPCRH<Self::ProgramProjectiveCurve, 41, 63>;
    type CommitmentGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 41, 63>;
    type Commitment = AleoLocator<<Self::CommitmentScheme as CRH>::Output, { Self::COMMITMENT_PREFIX }>;

    type FunctionIDCRH = PoseidonCRH<Self::InnerBaseField, 34>;
    type FunctionIDCRHGadget = PoseidonCRHGadget<Self::InnerBaseField, 34>;
    type FunctionID = AleoLocator<<Self::FunctionIDCRH as CRH>::Output, { Self::FUNCTION_ID_PREFIX }>;

    type FunctionInputsCRH = PoseidonCRH<Self::InnerScalarField, 128>;
    type FunctionInputsCRHGadget = PoseidonCRHGadget<Self::InnerScalarField, 128>;
    type FunctionInputsHash = AleoLocator<<Self::FunctionInputsCRH as CRH>::Output, { Self::FUNCTION_INPUTS_HASH_PREFIX }>;

    type InputCircuitIDCRH = BHPCRH<EdwardsBW6, 31, 63>;
    type InputCircuitID = AleoLocator<<Self::InputCircuitIDCRH as CRH>::Output, { Self::INPUT_CIRCUIT_ID_PREFIX }>;

    type OutputCircuitIDCRH = BHPCRH<EdwardsBW6, 27, 63>;
    type OutputCircuitID = AleoLocator<<Self::OutputCircuitIDCRH as CRH>::Output, { Self::OUTPUT_CIRCUIT_ID_PREFIX }>;

    type LedgerRootCRH = BHPCRH<Self::ProgramProjectiveCurve, 2, 43>;
    type LedgerRootCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 2, 43>;
    type LedgerRootTwoToOneCRH = BHPCRH<Self::ProgramProjectiveCurve, 3, 57>;
    type LedgerRootTwoToOneCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 3, 57>;
    type LedgerRootParameters = MerkleTreeParameters<Self::LedgerRootCRH, Self::LedgerRootTwoToOneCRH, { Self::LEDGER_TREE_DEPTH }>;
    type LedgerRoot = AleoLocator<<Self::LedgerRootCRH as CRH>::Output, { Self::LEDGER_ROOT_PREFIX }>;

    type PoSWMaskPRF = PoseidonPRF<Self::InnerScalarField, 4>;
    type PoSWMaskPRFGadget = PoseidonPRFGadget<Self::InnerScalarField, 4>;
    type PoSWNonce = AleoLocator<Self::InnerScalarField, { Self::HEADER_NONCE_PREFIX }>;

    type ProgramIDCRH = BHPCRH<Self::ProgramProjectiveCurve, 8, 16>;
    type ProgramIDTwoToOneCRH = BHPCRH<Self::ProgramProjectiveCurve, 8, 32>;
    type ProgramIDParameters = MerkleTreeParameters<Self::ProgramIDCRH, Self::ProgramIDTwoToOneCRH, { Self::PROGRAM_TREE_DEPTH }>;
    type ProgramID = AleoLocator<<Self::ProgramIDCRH as CRH>::Output, { Self::PROGRAM_ID_PREFIX }>;

    type RecordCiphertext = AleoObject<Ciphertext<Self>, { Self::RECORD_CIPHERTEXT_PREFIX }, { Self::RECORD_CIPHERTEXT_SIZE_IN_BYTES }>;
    type RecordRandomizer = AleoLocator<<Self::AccountEncryptionScheme as EncryptionScheme>::CiphertextRandomizer, { Self::RECORD_RANDOMIZER_PREFIX }>;
    type RecordViewKey = AleoObject<<Self::AccountEncryptionScheme as EncryptionScheme>::SymmetricKey, { Self::RECORD_VIEW_KEY_PREFIX }, { Self::RECORD_VIEW_KEY_SIZE_IN_BYTES }>;
    type RecordViewKeyCommitment = AleoLocator<<Self::AccountEncryptionScheme as EncryptionScheme>::SymmetricKeyCommitment, { Self::RECORD_VIEW_KEY_COMMITMENT_PREFIX }>;

    type SerialNumberPRF = PoseidonPRF<Self::InnerScalarField, 4>;
    type SerialNumberPRFGadget = PoseidonPRFGadget<Self::InnerScalarField, 4>;
    type SerialNumber = AleoLocator<<Self::SerialNumberPRF as PRF>::Output, { Self::SERIAL_NUMBER_PREFIX }>;

    type TransactionsRootCRH = BHPCRH<Self::ProgramProjectiveCurve, 2, 43>;
    type TransactionsRootCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 2, 43>;
    type TransactionsRootTwoToOneCRH = BHPCRH<Self::ProgramProjectiveCurve, 3, 57>;
    type TransactionsRootTwoToOneCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 3, 57>;
    type TransactionsRootParameters = MerkleTreeParameters<Self::TransactionsRootCRH, Self::TransactionsRootTwoToOneCRH, { Self::HEADER_TRANSACTIONS_TREE_DEPTH }>;
    type TransactionsRoot = AleoLocator<<Self::TransactionsRootCRH as CRH>::Output, { Self::HEADER_TRANSACTIONS_ROOT_PREFIX }>;

    type TransactionIDCRH = BHPCRH<Self::ProgramProjectiveCurve, 2, 43>;
    type TransactionIDCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 2, 43>;
    type TransactionIDTwoToOneCRH = BHPCRH<Self::ProgramProjectiveCurve, 3, 57>;
    type TransactionIDTwoToOneCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 3, 57>;
    type TransactionIDParameters = MerkleTreeParameters<Self::TransactionIDCRH, Self::TransactionIDTwoToOneCRH, { Self::TRANSACTION_TREE_DEPTH }>;
    type TransactionID = AleoLocator<<Self::TransactionIDCRH as CRH>::Output, { Self::TRANSACTION_ID_PREFIX }>;

    type TransitionIDCRH = BHPCRH<Self::ProgramProjectiveCurve, 2, 43>;
    type TransitionIDCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 2, 43>;
    type TransitionIDTwoToOneCRH = BHPCRH<Self::ProgramProjectiveCurve, 3, 57>;
    type TransitionIDTwoToOneCRHGadget = BHPCRHGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 3, 57>;
    type TransitionIDParameters = MerkleTreeParameters<Self::TransitionIDCRH, Self::TransactionIDTwoToOneCRH, { Self::TRANSITION_TREE_DEPTH }>;
    type TransitionID = AleoLocator<<Self::TransitionIDCRH as CRH>::Output, { Self::TRANSITION_ID_PREFIX }>;

    type ValueCommitmentScheme = PedersenCommitment<Self::ProgramProjectiveCurve, 4, 32>;
    type ValueCommitmentGadget = PedersenCommitmentGadget<Self::ProgramAffineCurve, Self::InnerScalarField, Self::ProgramAffineCurveGadget, 4, 32>;
    type ValueCommitment = AleoObject<<Self::ValueCommitmentScheme as CommitmentScheme>::Output, { Self::VALUE_COMMITMENT_PREFIX }, { Self::VALUE_COMMITMENT_SIZE_IN_BYTES }>;
    type ValueBalanceCommitment = AleoObject<ValueBalanceCommitment<Self>, { Self::VALUE_BALANCE_COMMITMENT_PREFIX }, { Self::VALUE_BALANCE_COMMITMENT_SIZE_IN_BYTES }>;

    dpc_setup!{Testnet2, account_encryption_scheme, AccountEncryptionScheme, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT}
    dpc_setup!{Testnet2, account_signature_scheme, AccountSignatureScheme, ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT}
    dpc_setup!{Testnet2, block_hash_crh, BlockHashCRH, "AleoBlockHashCRH0"}
    dpc_setup!{Testnet2, block_header_root_parameters, BlockHeaderRootParameters, "AleoBlockHeaderRootCRH0"}
    dpc_setup!{Testnet2, commitment_scheme, CommitmentScheme, "AleoCommitmentScheme0"}
    dpc_setup!{Testnet2, function_id_crh, FunctionIDCRH, "AleoFunctionIDCRH0"}
    dpc_setup!{Testnet2, ledger_root_parameters, LedgerRootParameters, "AleoLedgerRootCRH0"}
    dpc_setup!{Testnet2, program_id_parameters, ProgramIDParameters, "AleoProgramIDCRH0"}
    dpc_setup!{Testnet2, transactions_root_parameters, TransactionsRootParameters, "AleoTransactionsRootCRH0"}
    dpc_setup!{Testnet2, transaction_id_parameters, TransactionIDParameters, "AleoTransactionIDCRH0"}
    dpc_setup!{Testnet2, transition_id_parameters, TransitionIDParameters, "AleoTransitionIDCRH0"}
    dpc_setup!{Testnet2, value_commitment_scheme, ValueCommitmentScheme, "AleoValueCommitment0"}

    dpc_setup!{Testnet2, input_circuit_id_crh, InputCircuitIDCRH, "AleoInputCircuitIDCRH0"}
    dpc_setup!{Testnet2, output_circuit_id_crh, OutputCircuitIDCRH, "AleoOutputCircuitIDCRH0"}

    dpc_snark_setup!{Testnet2, input_proving_key, InputSNARK, ProvingKey, InputProvingKeyBytes, "input circuit proving key"}
    dpc_snark_setup!{Testnet2, input_verifying_key, InputSNARK, VerifyingKey, InputVerifyingKeyBytes, "input circuit verifying key"}
    
    dpc_snark_setup!{Testnet2, output_proving_key, OutputSNARK, ProvingKey, OutputProvingKeyBytes, "output circuit proving key"}
    dpc_snark_setup!{Testnet2, output_verifying_key, OutputSNARK, VerifyingKey, OutputVerifyingKeyBytes, "output circuit verifying key"}

    dpc_snark_setup!{Testnet2, posw_proving_key, PoSWSNARK, ProvingKey, PoSWProvingKeyBytes, "posw proving key"}
    dpc_snark_setup!{Testnet2, posw_verifying_key, PoSWSNARK, VerifyingKey, PoSWVerifyingKeyBytes, "posw verifying key"}

    fn input_circuit_id() -> &'static Self::InputCircuitID {
        static INPUT_CIRCUIT_ID: OnceCell<<Testnet2 as Network>::InputCircuitID> = OnceCell::new();
        INPUT_CIRCUIT_ID.get_or_init(|| Self::input_circuit_id_crh()
            .hash(&Self::input_verifying_key().to_minimal_bits())
            .expect("Failed to hash input circuit verifying key elements").into())
    }

    fn output_circuit_id() -> &'static Self::OutputCircuitID {
        static OUTPUT_CIRCUIT_ID: OnceCell<<Testnet2 as Network>::OutputCircuitID> = OnceCell::new();
        OUTPUT_CIRCUIT_ID.get_or_init(|| Self::output_circuit_id_crh()
            .hash(&Self::output_verifying_key().to_minimal_bits())
            .expect("Failed to hash output circuit verifying key elements").into())
    }

    fn posw() -> &'static Self::PoSW {
        static POSW: OnceCell<<Testnet2 as Network>::PoSW> = OnceCell::new();
        POSW.get_or_init(|| <Self::PoSW as PoSWScheme<Self>>::load(true).expect("Failed to load PoSW"))
    }
    
    fn genesis_block() -> &'static Block<Self> {
        static BLOCK: OnceCell<Block<Testnet2>> = OnceCell::new();
        BLOCK.get_or_init(|| FromBytes::read_le(&GenesisBlock::load_bytes()[..]).expect("Failed to load the genesis block"))
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
    fn test_input_circuit_sanity_check() {
        // Verify the input circuit verifying key matches the one derived from the input circuit proving key.
        assert_eq!(
            Testnet2::input_verifying_key(),
            &Testnet2::input_proving_key().circuit_verifying_key,
            "The input circuit verifying key does not correspond to the input circuit proving key"
        );
    }

    #[test]
    fn test_input_circuit_id_derivation() {
        // Verify the input circuit ID matches the one derived from the input circuit verifying key.
        assert_eq!(
            Testnet2::input_circuit_id(),
            &Testnet2::input_circuit_id_crh()
                .hash(&Testnet2::input_verifying_key().to_minimal_bits())
                .expect("Failed to hash input circuit ID")
                .into(),
            "The input circuit ID does not correspond to the input circuit verifying key"
        );
    }

    #[test]
    fn test_output_circuit_sanity_check() {
        // Verify the output circuit verifying key matches the one derived from the output circuit proving key.
        assert_eq!(
            Testnet2::output_verifying_key(),
            &Testnet2::output_proving_key().circuit_verifying_key,
            "The output circuit verifying key does not correspond to the output circuit proving key"
        );
    }

    #[test]
    fn test_output_circuit_id_derivation() {
        // Verify the output circuit ID matches the one derived from the output circuit verifying key.
        assert_eq!(
            Testnet2::output_circuit_id(),
            &Testnet2::output_circuit_id_crh()
                .hash(&Testnet2::output_verifying_key().to_minimal_bits())
                .expect("Failed to hash output circuit ID")
                .into(),
            "The output circuit ID does not correspond to the output circuit verifying key"
        );
    }

    #[test]
    fn test_posw_tree_sanity_check() {
        // Verify the PoSW tree depth matches the declared depth.
        assert_eq!(Testnet2::HEADER_TREE_DEPTH, 2); // Testnet2 has a tree depth of 2.
        assert_eq!(
            Testnet2::HEADER_TREE_DEPTH,
            <<Testnet2 as Network>::BlockHeaderRootParameters as MerkleParameters>::DEPTH
        );
    }
}
