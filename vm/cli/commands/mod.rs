// Copyright (C) 2019-2023 Aleo Systems Inc.
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

pub mod build;
pub use build::*;

pub mod clean;
pub use clean::*;

pub mod new;
pub use new::*;

pub mod run;
pub use run::*;

pub mod update;
pub use update::*;

use crate::{
    package::Package,
    prelude::{Identifier, Locator, ProgramID, Value},
};

use anyhow::Result;
use clap::Parser;
use colored::Colorize;
use core::str::FromStr;
use std::collections::HashMap;

pub(crate) type CurrentNetwork = crate::prelude::Testnet3;
pub(crate) type Aleo = crate::circuit::AleoV0;
