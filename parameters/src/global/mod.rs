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

// Commitments
impl_params_local!(
    LedgerMerkleTreeParameters,
    ledger_merkle_tree_test,
    "./",
    "ledger_merkle_tree",
    32804
);

// CRH
impl_params_local!(
    ProgramVKCRHParameters,
    program_vk_crh_test,
    "./",
    "program_vk_crh",
    1742404
);
impl_params_remote!(
    Testnet2ProgramVKCRHParameters,
    testnet2_program_vk_crh_test,
    "https://s3-us-west-1.amazonaws.com/aleo.parameters",
    "./",
    "testnet2_program_vk_crh",
    62930948
);
