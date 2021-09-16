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

use snarkvm_algorithms::{crypto_hash::PoseidonDefaultParametersField, prelude::*};
use snarkvm_dpc::Parameters;
use snarkvm_fields::PrimeField;
use snarkvm_gadgets::MaskedCRHGadget;
// use snarkvm_utilities::{FromBytes, ToBytes};

pub trait Network: 'static + Clone + PartialEq + Eq + Send + Sync {
    const MASKED_TREE_DEPTH: usize;

    const POSW_PROOF_SIZE_IN_BYTES: usize;

    type DPC: Parameters;
    type InnerScalarField: PrimeField + PoseidonDefaultParametersField;

    type CommitmentsTreeCRH: CRH;
    type CommitmentsTreeParameters: LoadableMerkleParameters<H = Self::CommitmentsTreeCRH>;

    type SerialNumbersTreeCRH: CRH;
    type SerialNumbersTreeParameters: LoadableMerkleParameters<H = Self::SerialNumbersTreeCRH>;

    type BlockHeaderCRH: CRH;

    type MerkleTreeCRH: CRH;

    /// Masked Merkle tree for Proof of Succinct Work (PoSW). Invoked only over `Self::InnerScalarField`.
    type MaskedMerkleTreeCRH: CRH;
    type MaskedMerkleTreeCRHGadget: MaskedCRHGadget<
        <Self::MaskedMerkleTreeParameters as MerkleParameters>::H,
        Self::InnerScalarField,
    >;
    // + CRHGadget<Self::MaskedMerkleTreeCRH, <Self::DPC as Parameters>::InnerScalarField>;
    type MaskedMerkleTreeParameters: MaskedMerkleParameters;

    /// SNARK proof system for PoSW.
    type PoswSNARK: SNARK<ScalarField = Self::InnerScalarField, VerifierInput = Vec<Self::InnerScalarField>>;

    fn block_header_crh() -> &'static Self::BlockHeaderCRH;
    fn merkle_tree_crh() -> &'static Self::MerkleTreeCRH;
    fn masked_merkle_tree_parameters() -> &'static Self::MaskedMerkleTreeParameters;
}
