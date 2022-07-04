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

#![forbid(unsafe_code)]
#![allow(clippy::module_inception)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
#![allow(clippy::explicit_auto_deref)]

#[macro_use]
extern crate derivative;
#[macro_use]
extern crate thiserror;

pub mod account;
pub use account::*;

pub mod block;
pub use block::*;

pub mod circuits;
pub use circuits::*;

pub mod errors;
pub use errors::*;

pub mod ledger;
pub use ledger::*;

pub mod network;
pub use network::*;

pub mod posw;
pub use posw::*;

pub mod record;
pub use record::*;

pub mod traits;
pub use traits::*;

pub mod transaction;
pub use transaction::*;

pub mod value_balance;
pub use value_balance::*;

pub mod virtual_machine;
pub use virtual_machine::*;

pub mod prelude {
    pub use crate::{
        account::*,
        block::*,
        errors::*,
        ledger::*,
        record::*,
        traits::*,
        transaction::*,
        value_balance::*,
        virtual_machine::*,
    };
}
