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

#[derive(Clone)]
pub struct DegreeInfo {
    /// max degree of the required SRS to commit to the polynomials
    pub max_degree: usize,
    /// max IOP poly degree used for (i)fft_precomputation
    pub max_fft_size: usize,
    /// degree bounds on IOP polynomials
    pub degree_bounds: Option<HashSet<usize>>,
    /// hiding bound for polynomial queries
    pub hiding_bound: usize,
    /// supported lagrange-basis SRS
    pub lagrange_sizes: Option<HashSet<usize>>,
}

impl DegreeInfo {
    pub fn union(self, other: &Self) -> Self {
        let hiding_bound = self.hiding_bound.max(other.hiding_bound);
        let max_degree = self.max_degree.max(other.max_degree);
        let max_fft_size = self.max_fft_size.max(other.max_fft_size);
        let mut new_bounds = self.degree_bounds.unwrap_or_default();
        if let Some(other_bounds) = &other.degree_bounds {
            new_bounds = &new_bounds | &other_bounds;
        }
        let degree_bounds = (!new_bounds.is_empty()).then_some(new_bounds);
        let mut new_l_sizes = self.lagrange_sizes.unwrap_or_default();
        if let Some(other_l_sizes) = &other.lagrange_sizes {
            new_l_sizes = &new_l_sizes | &other_l_sizes;
        }
        let lagrange_sizes = (!new_l_sizes.is_empty()).then_some(new_l_sizes);
        Self { max_degree, max_fft_size, degree_bounds, lagrange_sizes, hiding_bound }
    }
}
