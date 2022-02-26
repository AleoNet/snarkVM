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

#[cfg(feature = "cli")]
#[macro_use]
extern crate thiserror;

#[cfg(feature = "cli")]
pub mod cli;

#[cfg(feature = "algorithms")]
pub use snarkvm_algorithms as algorithms;

#[cfg(feature = "curves")]
pub use snarkvm_curves as curves;

#[cfg(feature = "dpc")]
pub use snarkvm_dpc as dpc;

#[cfg(feature = "fields")]
pub use snarkvm_fields as fields;

#[cfg(feature = "gadgets")]
pub use snarkvm_gadgets as gadgets;

#[cfg(feature = "ledger")]
pub use snarkvm_ledger as ledger;

#[cfg(feature = "parameters")]
pub use snarkvm_parameters as parameters;

#[cfg(feature = "r1cs")]
pub use snarkvm_r1cs as r1cs;

#[cfg(feature = "utilities")]
pub use snarkvm_utilities as utilities;

pub mod errors {
    #[cfg(feature = "algorithms")]
    pub use crate::algorithms::errors::*;

    #[cfg(feature = "curves")]
    pub use crate::curves::errors::*;

    #[cfg(feature = "dpc")]
    pub use crate::dpc::errors::*;

    #[cfg(feature = "fields")]
    pub use crate::fields::errors::*;

    #[cfg(feature = "gadgets")]
    pub use crate::gadgets::errors::*;

    #[cfg(feature = "ledger")]
    pub use crate::ledger::errors::*;

    #[cfg(feature = "parameters")]
    pub use crate::parameters::errors::*;

    #[cfg(feature = "r1cs")]
    pub use crate::r1cs::errors::*;

    #[cfg(feature = "utilities")]
    pub use crate::utilities::errors::*;
}

pub mod traits {
    #[cfg(feature = "algorithms")]
    pub use crate::algorithms::traits::*;

    #[cfg(feature = "curves")]
    pub use crate::curves::traits::*;

    #[cfg(feature = "dpc")]
    pub use crate::dpc::traits::*;

    #[cfg(feature = "fields")]
    pub use crate::fields::traits::*;

    #[cfg(feature = "gadgets")]
    pub use crate::gadgets::traits::*;

    #[cfg(feature = "ledger")]
    pub use crate::ledger::traits::*;

    #[cfg(feature = "parameters")]
    pub use crate::parameters::traits::*;
}

pub mod prelude {
    pub use crate::{errors::*, traits::*};

    #[cfg(feature = "algorithms")]
    pub use crate::algorithms::prelude::*;

    #[cfg(feature = "dpc")]
    pub use crate::dpc::prelude::*;

    #[cfg(feature = "ledger")]
    pub use crate::ledger::prelude::*;

    #[cfg(feature = "parameters")]
    pub use crate::parameters::prelude::*;

    #[cfg(feature = "r1cs")]
    pub use crate::r1cs::*;

    #[cfg(feature = "utilities")]
    pub use crate::utilities::*;
}
