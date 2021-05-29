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
    testnet1::{instantiated::Components, parameters::PublicParameters, BaseDPCComponents},
    traits::DPCComponents,
};
use snarkvm_algorithms::traits::{CRH, SNARK};
use snarkvm_utilities::{to_bytes, ToBytes};

fn testnet1_inner_circuit_id() -> anyhow::Result<Vec<u8>> {
    let parameters = PublicParameters::<Components>::load(false)?;

    let inner_snark_vk: <<Components as BaseDPCComponents>::InnerSNARK as SNARK>::VerificationParameters =
        parameters.inner_snark_parameters.1.clone().into();

    let inner_circuit_id = <<Components as DPCComponents>::InnerSNARKVerificationKeyCRH as CRH>::hash(
        &parameters.system_parameters.inner_snark_verification_key_crh,
        &to_bytes![inner_snark_vk]?,
    )?;

    Ok(to_bytes![inner_circuit_id]?)
}

#[test]
fn test_inner_circuit_sanity_check() {
    let expected_testnet1_inner_circuit_id = vec![
        132, 243, 19, 234, 73, 219, 14, 105, 124, 12, 23, 229, 144, 168, 24, 163, 93, 33, 139, 247, 16, 201, 132, 0,
        141, 28, 29, 2, 131, 75, 18, 78, 248, 57, 118, 61, 81, 53, 11, 91, 196, 233, 80, 186, 167, 144, 163, 0,
    ];
    let candidate_testnet1_inner_circuit_id = testnet1_inner_circuit_id().unwrap();
    assert_eq!(expected_testnet1_inner_circuit_id, candidate_testnet1_inner_circuit_id);
}
