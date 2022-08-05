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

// use crate::ledger::{
//     map::{memory_map::MemoryMap, Map, MapReader},
//     Deployment,
//     Origin,
//     Transition,
// };
//
// use console::{
//     network::prelude::*,
//     types::{Field, Group},
// };
//
// use anyhow::Result;
//
// /// A trait for transition storage.
// pub trait TransitionStorage<N: Network>: Clone {
//     type DeploymentsMap: for<'a> Map<'a, N::TransitionID, (Deployment<N>, N::TransitionID)>;
//     type ExecutionsMap: for<'a> Map<'a, N::TransitionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>;
//     type TransitionsMap: for<'a> Map<'a, N::TransitionID, Transition<N>>;
//     type TransitionPublicKeysMap: for<'a> Map<'a, Group<N>, N::TransitionID>;
//     type SerialNumbersMap: for<'a> Map<'a, Field<N>, N::TransitionID>;
//     type CommitmentsMap: for<'a> Map<'a, Field<N>, N::TransitionID>;
//     type OriginsMap: for<'a> Map<'a, Origin<N>, N::TransitionID>;
//     type NonceMap: for<'a> Map<'a, Group<N>, N::TransitionID>;
// }
//
// /// An in-memory transition storage.
// #[derive(Clone)]
// pub struct TransitionMemory<N: Network>(core::marker::PhantomData<N>);
//
// #[rustfmt::skip]
// impl<N: Network> TransitionStorage<N> for TransitionMemory<N> {
//     type DeploymentsMap = MemoryMap<N::TransitionID, (Deployment<N>, N::TransitionID)>;
//     type ExecutionsMap = MemoryMap<N::TransitionID, (Vec<N::TransitionID>, Option<N::TransitionID>)>;
//     type TransitionsMap = MemoryMap<N::TransitionID, Transition<N>>;
//     type TransitionPublicKeysMap = MemoryMap<Group<N>, N::TransitionID>;
//     type SerialNumbersMap = MemoryMap<Field<N>, N::TransitionID>;
//     type CommitmentsMap = MemoryMap<Field<N>, N::TransitionID>;
//     type OriginsMap = MemoryMap<Origin<N>, N::TransitionID>;
//     type NonceMap = MemoryMap<Group<N>, N::TransitionID>;
// }
//
// /// The transition state stored in a ledger.
// /// `TransitionPublicKeysMap`, `SerialNumbersMap`, `CommitmentsMap`, `OriginsMap`, and `NonceMap` store redundant data for faster lookup.
// #[derive(Clone)]
// pub struct TransitionStore<N: Network, T: TransitionStorage<N>> {
//     /// The map of program deployments.
//     deployments: T::DeploymentsMap,
//     /// The map of program executions.
//     executions: T::ExecutionsMap,
//     /// The map of transitions.
//     transitions: T::TransitionsMap,
//     /// The map of serial numbers.
//     transition_public_keys: T::TransitionPublicKeysMap,
//     /// The map of origins.
//     origins: T::OriginsMap,
//     /// The map of serial numbers.
//     serial_numbers: T::SerialNumbersMap,
//     /// The map of commitments.
//     commitments: T::CommitmentsMap,
//     /// The map of nonces.
//     nonces: T::NonceMap,
// }
//
// impl<N: Network> TransitionStore<N, TransitionMemory<N>> {
//     /// Initializes a new instance of `TransitionStore`.
//     pub fn new() -> Self {
//         Self {
//             deployments: Default::default(),
//             executions: Default::default(),
//             transitions: Default::default(),
//             transition_public_keys: Default::default(),
//             origins: Default::default(),
//             serial_numbers: Default::default(),
//             commitments: Default::default(),
//             nonces: Default::default(),
//         }
//     }
// }
//
// impl<N: Network, T: TransitionStorage<N>> TransitionStore<N, T> {
//     /// Initializes a new instance of `TransitionStore` from the given maps.
//     pub fn from_maps(
//         deployments: T::DeploymentsMap,
//         executions: T::ExecutionsMap,
//         transitions: T::TransitionsMap,
//         transition_public_keys: T::TransitionPublicKeysMap,
//         origins: T::OriginsMap,
//         serial_numbers: T::SerialNumbersMap,
//         commitments: T::CommitmentsMap,
//         nonces: T::NonceMap,
//     ) -> Result<Self> {
//         let transition_store = Self {
//             deployments,
//             executions,
//             transitions,
//             transition_public_keys,
//             origins,
//             serial_numbers,
//             commitments,
//             nonces,
//         };
//
//         // TODO (raychu86): Enforce that all the transition state is valid.
//
//         Ok(transition_store)
//     }
// }
