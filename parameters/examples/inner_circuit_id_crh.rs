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

use snarkvm_algorithms::{errors::CRHError, traits::CRH};
use snarkvm_dpc::{testnet1::instantiated::Components, traits::DPCComponents};
use snarkvm_utilities::ToBytes;

use std::path::PathBuf;

mod utils;
use utils::store;

pub fn setup<C: DPCComponents>() -> Result<Vec<u8>, CRHError> {
    let inner_circuit_id_crh = <C::InnerCircuitIDCRH as CRH>::setup("InnerCircuitIDCRH");
    let inner_circuit_id_crh_parameters_bytes = inner_circuit_id_crh.to_bytes_le()?;

    let size = inner_circuit_id_crh_parameters_bytes.len();
    println!("inner_circuit_id_crh.params\n\tsize - {}", size);
    Ok(inner_circuit_id_crh_parameters_bytes)
}

pub fn main() {
    let bytes = setup::<Components>().unwrap();
    let filename = PathBuf::from("inner_circuit_id_crh.params");
    let sumname = PathBuf::from("inner_circuit_id_crh.checksum");
    store(&filename, &sumname, &bytes).unwrap();
}
