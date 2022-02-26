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

use crate::{boxed::Box, vec::Vec};

pub struct ExecutionPool<'a, T> {
    #[cfg(feature = "parallel")]
    jobs: Vec<Box<dyn 'a + FnOnce() -> T + Send>>,
    #[cfg(not(feature = "parallel"))]
    jobs: Vec<Box<dyn 'a + FnOnce() -> T>>,
}

impl<'a, T> ExecutionPool<'a, T> {
    pub fn new() -> Self {
        Self { jobs: Vec::new() }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self { jobs: Vec::with_capacity(cap) }
    }

    #[cfg(feature = "parallel")]
    pub fn add_job<F: 'a + FnOnce() -> T + Send>(&mut self, f: F) {
        self.jobs.push(Box::new(f));
    }

    #[cfg(not(feature = "parallel"))]
    pub fn add_job<F: 'a + FnOnce() -> T>(&mut self, f: F) {
        self.jobs.push(Box::new(f));
    }

    pub fn execute_all(self) -> Vec<T>
    where
        T: Send + Sync,
    {
        #[cfg(feature = "parallel")]
        {
            use rayon::prelude::*;
            execute_with_max_available_threads(|| self.jobs.into_par_iter().map(|f| f()).collect())
        }
        #[cfg(not(feature = "parallel"))]
        {
            self.jobs.into_iter().map(|f| f()).collect()
        }
    }
}

impl<'a, T> Default for ExecutionPool<'a, T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "parallel")]
pub fn max_available_threads() -> usize {
    use aleo_std::Cpu;
    let rayon_threads = rayon::current_num_threads();

    match aleo_std::get_cpu() {
        Cpu::Intel => num_cpus::get_physical().min(rayon_threads),
        Cpu::AMD | Cpu::Unknown => rayon_threads,
    }
}

#[inline(always)]
#[cfg(feature = "parallel")]
pub fn execute_with_max_available_threads<T: Sync + Send>(f: impl FnOnce() -> T + Send) -> T {
    execute_with_threads(f, max_available_threads())
}

#[inline(always)]
#[cfg(not(feature = "parallel"))]
pub fn execute_with_max_available_threads<T>(f: impl FnOnce() -> T + Send) -> T {
    f()
}

#[cfg(feature = "parallel")]
#[inline(always)]
fn execute_with_threads<T: Sync + Send>(f: impl FnOnce() -> T + Send, num_threads: usize) -> T {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(num_threads).build().unwrap();
    pool.install(f)
}

/// Creates parallel iterator over refs if `parallel` feature is enabled.
#[macro_export]
macro_rules! cfg_iter {
    ($e: expr) => {{
        #[cfg(feature = "parallel")]
        let result = $e.par_iter();

        #[cfg(not(feature = "parallel"))]
        let result = $e.iter();

        result
    }};
}

/// Creates parallel iterator over mut refs if `parallel` feature is enabled.
#[macro_export]
macro_rules! cfg_iter_mut {
    ($e: expr) => {{
        #[cfg(feature = "parallel")]
        let result = $e.par_iter_mut();

        #[cfg(not(feature = "parallel"))]
        let result = $e.iter_mut();

        result
    }};
}

/// Creates parallel iterator if `parallel` feature is enabled.
#[macro_export]
macro_rules! cfg_into_iter {
    ($e: expr) => {{
        #[cfg(feature = "parallel")]
        let result = $e.into_par_iter();

        #[cfg(not(feature = "parallel"))]
        let result = $e.into_iter();

        result
    }};
}

/// Returns an iterator over `chunk_size` elements of the slice at a
/// time.
#[macro_export]
macro_rules! cfg_chunks {
    ($e: expr, $size: expr) => {{
        #[cfg(feature = "parallel")]
        let result = $e.par_chunks($size);

        #[cfg(not(feature = "parallel"))]
        let result = $e.chunks($size);

        result
    }};
}

/// Returns an iterator over `chunk_size` elements of the slice at a time.
#[macro_export]
macro_rules! cfg_chunks_mut {
    ($e: expr, $size: expr) => {{
        #[cfg(feature = "parallel")]
        let result = $e.par_chunks_mut($size);

        #[cfg(not(feature = "parallel"))]
        let result = $e.chunks_mut($size);

        result
    }};
}

/// Applies the reduce operation over an iterator.
#[macro_export]
macro_rules! cfg_reduce {
    ($e: expr, $default: expr, $op: expr) => {{
        #[cfg(feature = "parallel")]
        let result = $e.reduce($default, $op);

        #[cfg(not(feature = "parallel"))]
        let result = $e.fold($default(), $op);

        result
    }};
}
