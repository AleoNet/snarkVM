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

pub static ACCOUNT_ENCRYPTION_AND_SIGNATURE_INPUT: &str = "AleoAccountEncryptionAndSignatureScheme0";
pub static ACCOUNT_SEED_SK_SIG_DOMAIN: &str = "AleoAccountSeedSignatureSecretKey0";
pub static ACCOUNT_SEED_R_SIG_DOMAIN: &str = "AleoAccountSeedSignatureRandomizer0";

pub static PRIVATE_KEY_PREFIX: [u8; 11] = [127, 134, 189, 116, 210, 221, 210, 137, 145, 18, 253]; // APrivateKey1
pub static _COMPUTE_KEY_PREFIX: [u8; 10] = [109, 249, 98, 224, 36, 15, 213, 187, 79, 190]; // AComputeKey1
pub static VIEW_KEY_PREFIX: [u8; 7] = [14, 138, 223, 204, 247, 224, 122]; // AViewKey1
pub static ADDRESS_PREFIX: &str = "aleo";
