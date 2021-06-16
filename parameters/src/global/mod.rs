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
    AccountCommitmentParameters,
    account_commitment_test,
    "./",
    "account_commitment",
    417868
);
impl_params_local!(
    AccountSignatureParameters,
    account_signature_test,
    "./",
    "account_signature",
    16420
);
impl_params_local!(
    LedgerMerkleTreeParameters,
    ledger_merkle_tree_test,
    "./",
    "ledger_merkle_tree",
    32804
);
impl_params_local!(
    LocalDataCommitmentParameters,
    local_data_commitment_test,
    "./",
    "local_data_commitment",
    280780
);
impl_params_local!(
    RecordCommitmentParameters,
    record_commitment_test,
    "./",
    "record_commitment",
    507084
);

// CRH
impl_params_local!(
    EncryptedRecordCRHParameters,
    encrypted_record_crh_test,
    "./",
    "encrypted_record_crh",
    270532
);
impl_params_local!(
    InnerCircuitIDCRH,
    inner_circuit_id_crh_test,
    "./",
    "inner_circuit_id_crh",
    3581604
);
impl_params_local!(
    LocalDataCRHParameters,
    local_data_crh_test,
    "./",
    "local_data_crh",
    65604
);
impl_params_local!(
    ProgramVKCRHParameters,
    program_vk_crh_test,
    "./",
    "program_vk_crh",
    1742404
);
impl_params_local!(
    Testnet2ProgramVKCRHParameters,
    testnet2_program_vk_crh_test,
    "./",
    "testnet2_program_vk_crh",
    62930948
);

impl_params_local!(
    SerialNumberNonceCRHParameters,
    serial_number_nonce_crh_test,
    "./",
    "serial_number_nonce_crh",
    258180
);

// Encryption
impl_params_local!(
    AccountEncryptionParameters,
    account_encryption_test,
    "./",
    "account_encryption",
    32804
);
