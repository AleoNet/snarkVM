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

#![no_main]
#[macro_use] extern crate libfuzzer_sys;

use snarkvm_instructions::Integer;

fuzz_target!(|data: &[u8]| {
    // let input = format!("{}u_8", data[0]);
    // let _ = Integer::new(input.as_str()).unwrap();

    let _ = Integer::new("123u8").unwrap();

    // if let Ok(s) = std::str::from_utf8(data) {
    // }
});
