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

use crate::ahp::verifier::{VerifierFirstMessage, VerifierSecondMessage};
use snarkvm_algorithms::fft::EvaluationDomain;
use snarkvm_curves::traits::PrimeField;

/// State of the AHP verifier.
pub struct VerifierState<F: PrimeField> {
    pub(crate) domain_h: EvaluationDomain<F>,
    pub(crate) domain_k: EvaluationDomain<F>,

    pub(crate) first_round_message: Option<VerifierFirstMessage<F>>,
    pub(crate) second_round_message: Option<VerifierSecondMessage<F>>,

    pub(crate) gamma: Option<F>,
}
