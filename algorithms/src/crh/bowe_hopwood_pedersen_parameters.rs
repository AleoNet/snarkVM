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

use snarkvm_curves::Group;

use super::{PedersenCRHParameters, PedersenSize};

pub const BOWE_HOPWOOD_CHUNK_SIZE: usize = 3;
pub const BOWE_HOPWOOD_LOOKUP_SIZE: usize = 2usize.pow(BOWE_HOPWOOD_CHUNK_SIZE as u32);

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use once_cell::sync::OnceCell;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoweHopwoodPedersenCRHParameters<G: Group> {
    base_lookup: OnceCell<Vec<Vec<[G; BOWE_HOPWOOD_LOOKUP_SIZE]>>>,
}

impl<G: Group> BoweHopwoodPedersenCRHParameters<G> {
    pub fn new() -> Self {
        Self {
            base_lookup: OnceCell::new(),
        }
    }

    pub fn base_lookup<S: PedersenSize>(
        &self,
        input: &PedersenCRHParameters<G, S>,
    ) -> &Vec<Vec<[G; BOWE_HOPWOOD_LOOKUP_SIZE]>> {
        self.base_lookup
            .get_or_try_init::<_, ()>(|| {
                Ok(cfg_iter!(input.bases)
                    .map(|x| {
                        x.iter()
                            .map(|g| {
                                let mut out = [G::zero(); BOWE_HOPWOOD_LOOKUP_SIZE];
                                for i in 0..BOWE_HOPWOOD_LOOKUP_SIZE {
                                    let mut encoded = *g;
                                    if (i & 0x01) != 0 {
                                        encoded += g;
                                    }
                                    if (i & 0x02) != 0 {
                                        encoded += &g.double();
                                    }
                                    if (i & 0x04) != 0 {
                                        encoded = encoded.neg();
                                    }
                                    out[i] = encoded;
                                }
                                out
                            })
                            .collect()
                    })
                    .collect())
            })
            .expect("failed to init BoweHopwoodPedersenCRHParameters")
    }
}
