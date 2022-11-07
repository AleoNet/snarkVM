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

#![cfg_attr(not(feature = "aleo-cli"), allow(unused_variables))]

use console::{
    network::{prelude::*, FiatShamir},
    program::Identifier,
};
use snarkvm_algorithms::{snark::marlin, traits::SNARK};

use once_cell::sync::OnceCell;
use std::sync::Arc;

#[cfg(feature = "aleo-cli")]
use colored::Colorize;

type Marlin<N> = marlin::MarlinSNARK<<N as Environment>::PairingCurve, FiatShamir<N>, marlin::MarlinHidingMode>;

mod certificate;
pub use certificate::Certificate;

mod proof;
pub use proof::Proof;

mod proving_key;
pub use proving_key::ProvingKey;

mod universal_srs;
pub use universal_srs::UniversalSRS;

mod verifying_key;
pub use verifying_key::VerifyingKey;
