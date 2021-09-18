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

use snarkvm_algorithms::{
    crh::{BHPCompressedCRH, PedersenCompressedCRH},
    define_masked_merkle_tree_parameters,
};
use snarkvm_dpc::{testnet1::Testnet1, Network};
use snarkvm_gadgets::algorithms::crh::PedersenCompressedCRHGadget;
// use snarkvm_utilities::{FromBytes, ToBytes};
use snarkvm_marlin::{constraints::snark::MarlinSNARK, marlin::MarlinTestnet1Mode, FiatShamirChaChaRng};
use snarkvm_polycommit::sonic_pc::SonicKZG10;

use blake2::Blake2s;
use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};

define_masked_merkle_tree_parameters!(
    MaskedMerkleTreeParameters,
    <Testnet1 as Network>::MaskedMerkleTreeCRH,
    <Testnet1 as Network>::MASKED_TREE_DEPTH
);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Testnet1;

#[rustfmt::skip]
impl Network for Testnet1 {
    /// A masked Merkle tree with depth = 2. This may change in the future.
    const MASKED_TREE_DEPTH: usize = 2;
    
    type DPC = Testnet1;
    type InnerScalarField = <Self::DPC as Network>::InnerScalarField;
    
    /// A masked Merkle tree instantiated with the masked Pedersen hash over BLS12-377.
    type MaskedMerkleTreeCRH = PedersenCompressedCRH<<<Testnet1 as Network>::DPC as Network>::ProgramProjectiveCurve, 4, 128>;
    type MaskedMerkleTreeCRHGadget = PedersenCompressedCRHGadget<
        <Self::DPC as Network>::ProgramProjectiveCurve,
        Self::InnerScalarField,
        <Self::DPC as Network>::ProgramAffineCurveGadget,
        4,
        128
    >;
    type MaskedMerkleTreeParameters = MaskedMerkleTreeParameters;

    /// SNARK proof system for PoSW.
    type PoswSNARK = MarlinSNARK<
        Self::InnerScalarField,
        <<Self as Network>::DPC as Network>::OuterScalarField,
        SonicKZG10<<<Self as Network>::DPC as Network>::InnerCurve>,
        FiatShamirChaChaRng<
            Self::InnerScalarField,
            <<Self as Network>::DPC as Network>::OuterScalarField,
            Blake2s,
        >,
        MarlinTestnet1Mode,
        Vec<Self::InnerScalarField>,
    >;

    fn masked_merkle_tree_parameters() -> &'static Self::MaskedMerkleTreeParameters {
        static MASKED_MERKLE_TREE_PARAMETERS: OnceCell<MaskedMerkleTreeParameters> = OnceCell::new();
        MASKED_MERKLE_TREE_PARAMETERS.get_or_init(|| MaskedMerkleTreeParameters::setup("MerkleTreeParameters"))
    }
}
