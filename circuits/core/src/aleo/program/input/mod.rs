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

// #[cfg(test)]
// use snarkvm_circuits_types::environment::assert_scope;

// use crate::{
//     aleo::{Aleo, Record},
//     algorithms::MerklePath,
// };
// use snarkvm_circuits_types::{environment::prelude::*, Address, Field, U64};
//
// pub struct InputPublic<A: Aleo> {
//     serial_number: Field<A>,
//     ledger_root: Field<A>,
// }
//
// pub struct InputPrivate<A: Aleo> {
//     record: Record<A>,
//     // merkle_proof: MerklePath<A>,
// }
//
// pub struct Input;
//
// impl Input {
//     pub fn execute<A: Aleo>(public: InputPublic<A>, private: InputPrivate<A>) {
//         // let commitment = private.record.to_state().to_commitment();
//         // A::assert_eq(public.serial_number, private.record.to_serial_number());
//     }
// }
//
// impl TypeName for Input {
//     fn type_name() -> &'static str {
//         "input"
//     }
// }
