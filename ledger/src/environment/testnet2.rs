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

use crate::Environment;
use snarkvm_dpc::{
    testnet2::Testnet2 as Testnet2Network,
    CommitmentsTree,
    CommitmentsTreeScheme,
    SerialNumbersTree,
    SerialNumbersTreeScheme,
};

use once_cell::sync::OnceCell;

pub struct Testnet2;

impl Environment for Testnet2 {
    type CommitmentsTree = CommitmentsTree<Self::Network>;
    type Network = Testnet2Network;
    type SerialNumbersTree = SerialNumbersTree<Self::Network>;

    fn commitments_tree() -> &'static Self::CommitmentsTree {
        static TREE: OnceCell<<Testnet2 as Environment>::CommitmentsTree> = OnceCell::new();
        TREE.get_or_init(|| {
            <Self::CommitmentsTree as CommitmentsTreeScheme<Self::Network>>::new()
                .expect("Failed to load the commitments tree")
        })
    }

    fn serial_numbers_tree() -> &'static Self::SerialNumbersTree {
        static TREE: OnceCell<<Testnet2 as Environment>::SerialNumbersTree> = OnceCell::new();
        TREE.get_or_init(|| {
            <Self::SerialNumbersTree as SerialNumbersTreeScheme<Self::Network>>::new()
                .expect("Failed to load the serial numbers tree")
        })
    }
}
