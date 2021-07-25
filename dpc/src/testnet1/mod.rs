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

pub mod dpc;
pub use dpc::*;

pub mod outer_circuit;
pub use outer_circuit::*;

pub mod parameters;

use crate::Parameters;
use snarkvm_gadgets::{bits::Boolean, traits::algorithms::SNARKVerifierGadget};

/// Trait that stores information about the testnet1 DPC scheme.
pub trait Testnet1Components: Parameters {
    /// SNARK Verifier gadget for the inner circuit.
    type InnerSNARKGadget: SNARKVerifierGadget<Self::InnerSNARK, Input = Vec<Boolean>>;

    /// Program SNARK verifier gadget for Aleo applications.
    type ProgramSNARKGadget: SNARKVerifierGadget<Self::ProgramSNARK, Input = Vec<Boolean>>;
}
