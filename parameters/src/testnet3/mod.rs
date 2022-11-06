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

pub mod genesis;
pub use genesis::*;

pub mod powers;
pub use powers::*;

const REMOTE_URL: &str = "https://vm.aleo.org/testnet3/parameters";

// Degree 15
impl_local!(Degree15, "resources/", "universal", "srs", "15");
// Degree 16
impl_remote!(Degree16, REMOTE_URL, "resources/", "universal", "srs", "16");
// Degree 17
impl_remote!(Degree17, REMOTE_URL, "resources/", "universal", "srs", "17");
// Degree 18
impl_remote!(Degree18, REMOTE_URL, "resources/", "universal", "srs", "18");
// Degree 19
impl_remote!(Degree19, REMOTE_URL, "resources/", "universal", "srs", "19");
// Degree 20
impl_remote!(Degree20, REMOTE_URL, "resources/", "universal", "srs", "20");
// Degree 21
impl_remote!(Degree21, REMOTE_URL, "resources/", "universal", "srs", "21");
// Degree 22
impl_remote!(Degree22, REMOTE_URL, "resources/", "universal", "srs", "22");
// Degree 23
impl_remote!(Degree23, REMOTE_URL, "resources/", "universal", "srs", "23");
// Degree 24
impl_remote!(Degree24, REMOTE_URL, "resources/", "universal", "srs", "24");
// Degree 25
impl_remote!(Degree25, REMOTE_URL, "resources/", "universal", "srs", "25");
// Degree 26
impl_remote!(Degree26, REMOTE_URL, "resources/", "universal", "srs", "26");
// Degree 27
impl_remote!(Degree27, REMOTE_URL, "resources/", "universal", "srs", "27");
// Degree 28
impl_remote!(Degree28, REMOTE_URL, "resources/", "universal", "srs", "28");
// Gamma
impl_local!(Gamma, "resources/", "universal", "srs", "gamma");

// Trial
impl_remote!(TrialSRS, REMOTE_URL, "resources/", "universal", "srs", "trial");

macro_rules! impl_remote_keys {
    ($pname: ident, $vname: ident, $fname: tt) => {
        impl_remote!($pname, REMOTE_URL, "resources/", $fname, "prover");
        impl_remote!($vname, REMOTE_URL, "resources/", $fname, "verifier");
    };
}

// Mint
impl_remote_keys!(MintProver, MintVerifier, "mint");
// Transfer
impl_remote_keys!(TransferProver, TransferVerifier, "transfer");
// Join
impl_remote_keys!(JoinProver, JoinVerifier, "join");
// Split
impl_remote_keys!(SplitProver, SplitVerifier, "split");
// Fee
impl_remote_keys!(FeeProver, FeeVerifier, "fee");

lazy_static! {
    pub static ref TESTNET3_CREDITS_PROGRAM: indexmap::IndexMap<String, (Vec<u8>, Vec<u8>)> = {
        macro_rules! insert_remote_keys {
            ($map: ident, $pname: ident, $vname: ident, $fname: tt) => {
                $map.insert(
                    $fname.to_string(),
                    (
                        $pname::load_bytes().expect("Failed to load proving key"),
                        $vname::load_bytes().expect("Failed to load verifying key"),
                    ),
                );
            };
        }
        let mut map = indexmap::IndexMap::new();
        insert_remote_keys!(map, MintProver, MintVerifier, "mint");
        insert_remote_keys!(map, TransferProver, TransferVerifier, "transfer");
        insert_remote_keys!(map, JoinProver, JoinVerifier, "join");
        insert_remote_keys!(map, SplitProver, SplitVerifier, "split");
        insert_remote_keys!(map, FeeProver, FeeVerifier, "fee");
        map
    };
}

// Inclusion
impl_remote_keys!(InclusionProver, InclusionVerifier, "inclusion");

/// The function name for the inclusion circuit.
pub const TESTNET3_INCLUSION_FUNCTION_NAME: &str = "inclusion";

lazy_static! {
    pub static ref TESTNET3_INCLUSION_PROVING_KEY: Vec<u8> =
        InclusionProver::load_bytes().expect("Failed to load inclusion proving key");
    pub static ref TESTNET3_INCLUSION_VERIFYING_KEY: Vec<u8> =
        InclusionVerifier::load_bytes().expect("Failed to load inclusion verifying key");
}
