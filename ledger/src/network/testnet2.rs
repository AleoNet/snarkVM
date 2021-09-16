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

use crate::Network;
use snarkvm_algorithms::{crh::BHPCompressedCRH, prelude::*};
use snarkvm_dpc::testnet2::Testnet2Parameters;
// use snarkvm_utilities::{FromBytes, ToBytes};

use snarkvm_curves::edwards_bls12::EdwardsProjective as EdwardsBls;

use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Testnet2;

impl Network for Testnet2 {
    type BlockHeaderCRH = BHPCompressedCRH<EdwardsBls, 117, 63>;
    type DPC = Testnet2Parameters;

    const POSW_PROOF_SIZE_IN_BYTES: usize = 771;

    fn block_header_crh() -> &'static Self::BlockHeaderCRH {
        static BLOCK_HEADER_CRH: OnceCell<<Testnet2 as Network>::BlockHeaderCRH> = OnceCell::new();
        BLOCK_HEADER_CRH.get_or_init(|| Self::BlockHeaderCRH::setup("BlockHeaderCRH"))
    }
}
