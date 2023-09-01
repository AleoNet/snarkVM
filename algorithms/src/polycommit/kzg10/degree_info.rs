// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::HashSet;

#[derive(Default)]
pub struct DegreeInfo {
    /// max degree of the required SRS to commit to the polynomials
    pub max_degree: usize,
    /// max IOP poly degree used for (i)fft_precomputation
    pub max_fft_size: usize,
    /// degree bounds on IOP polynomials
    pub degree_bounds: HashSet<usize>,
}

impl DegreeInfo {
    pub fn union(&mut self, other: &Self) {
        self.max_degree = self.max_degree.max(other.max_degree);
        self.max_fft_size = self.max_fft_size.max(other.max_fft_size);
        for &coeff in &other.degree_bounds {
            self.degree_bounds.insert(coeff);
        }
    }
}
