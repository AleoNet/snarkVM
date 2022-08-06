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

mod input;
use input::*;

mod output;
use output::*;

// use crate::ledger::{
//     map::{memory_map::MemoryMap, Map, MapReader},
//     Transition,
// };
// use console::network::prelude::*;
//
// use anyhow::Result;
// use std::borrow::Cow;
//
// /// A trait for transition input storage.
// pub trait TransitionStorage<N: Network> {
//     /// The plaintext hash and (optional) plaintext.
//     type ConstantMap: for<'a> Map<'a, N::TransitionID, Transition<N>>;
//     /// The plaintext hash and (optional) plaintext.
//     type PublicMap: for<'a> Map<'a, N::TransitionID, Transition<N>>;
//     /// The ciphertext hash and (optional) ciphertext.
//     type PrivateMap: for<'a> Map<'a, N::TransitionID, Transition<N>>;
//     /// The serial number, tag, and the origin of the record.
//     type RecordMap: for<'a> Map<'a, N::TransitionID, Transition<N>>;
//     /// The input commitment to the external record. Note: This is **not** the record commitment.
//     type ExternalRecordMap: for<'a> Map<'a, N::TransitionID, Transition<N>>;
// }
//
// /// An in-memory transition input storage.
// #[derive(Clone)]
// pub struct TransitionMemory<N: Network>(core::marker::PhantomData<N>);
//
// #[rustfmt::skip]
// impl<N: Network> TransitionStorage<N> for TransitionMemory<N> {
//     type ConstantMap = MemoryMap<N::TransitionID, Transition<N>>;
//     type PublicMap = MemoryMap<N::TransitionID, Transition<N>>;
//     type PrivateMap = MemoryMap<N::TransitionID, Transition<N>>;
//     type RecordMap = MemoryMap<N::TransitionID, Transition<N>>;
//     type ExternalRecordMap = MemoryMap<N::TransitionID, Transition<N>>;
// }
