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

use console::{network::prelude::*, program::Identifier};
use snarkvm_algorithms::{crypto_hash::PoseidonSponge, snark::marlin, SNARK};
use snarkvm_curves::PairingEngine;
use snarkvm_utilities::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};

use colored::Colorize;
use std::sync::Arc;

type Fq<N> = <<N as Environment>::PairingCurve as PairingEngine>::Fq;
type Fr<N> = <N as Environment>::Field;
type FS<N> = marlin::fiat_shamir::FiatShamirAlgebraicSpongeRng<Fr<N>, Fq<N>, PoseidonSponge<Fq<N>, 6, 1>>;
type Marlin<N> = marlin::MarlinSNARK<<N as Environment>::PairingCurve, FS<N>, marlin::MarlinHidingMode, [Fr<N>]>;

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
