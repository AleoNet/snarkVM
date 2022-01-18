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

use crate::{boxed::Box, vec::Vec};
pub struct ExecutionPool<'a, T> {
    #[cfg(feature = "parallel")]
    tasks: Vec<Box<dyn 'a + FnOnce() -> T + Send>>,
    #[cfg(not(feature = "parallel"))]
    tasks: Vec<Box<dyn 'a + FnOnce() -> T>>,
}

impl<'a, T> ExecutionPool<'a, T> {
    pub fn new() -> Self {
        Self { tasks: Vec::new() }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            tasks: Vec::with_capacity(cap),
        }
    }

    #[cfg(feature = "parallel")]
    pub fn add_task<F: 'a + FnOnce() -> T + Send>(&mut self, f: F) {
        self.tasks.push(Box::new(f));
    }

    #[cfg(not(feature = "parallel"))]
    pub fn add_task<F: 'a + FnOnce() -> T>(&mut self, f: F) {
        self.tasks.push(Box::new(f));
    }

    pub fn execute_all(self) -> Vec<T>
    where
        T: Send + Sync,
    {
        #[cfg(feature = "parallel")]
        {
            use itertools::Itertools;
            // At most 12 threads per task
            const THREADS_PER_TASK: usize = 12;
            let threads_per_task = if rayon::current_num_threads() > self.tasks.len() * THREADS_PER_TASK {
                rayon::current_num_threads() / self.tasks.len()
            } else {
                THREADS_PER_TASK.min(rayon::current_num_threads())
            };
            let task_chunk_size = rayon::current_num_threads() / threads_per_task
                + usize::from(rayon::current_num_threads() % threads_per_task != 0);

            if (threads_per_task as f64 / rayon::current_num_threads() as f64) < 1.0 {
                use std::sync::{Arc, RwLock};
                let mut task_results = Vec::with_capacity(self.tasks.len());
                for _ in 0..self.tasks.len() {
                    task_results.push(RwLock::new(None));
                }
                let task_results = Arc::new(task_results);
                self.tasks
                    .into_iter()
                    .chunks(task_chunk_size)
                    .into_iter()
                    .enumerate()
                    .for_each(|(i, task_set): (usize, _)| {
                        let task_set = task_set.collect::<Vec<_>>();
                        rayon::scope(|s| {
                            let mut remaining_threads = rayon::current_num_threads();
                            for (j, task) in task_set.into_iter().enumerate() {
                                let num_threads = remaining_threads
                                    .checked_sub(threads_per_task)
                                    .map_or(remaining_threads, |_| threads_per_task);
                                let task_results_scoped = Arc::clone(&task_results);
                                s.spawn(move |_| {
                                    rayon::ThreadPoolBuilder::new()
                                        .num_threads(num_threads)
                                        .build()
                                        .expect("could not build threadpool")
                                        .install(|| {
                                            let result = task();
                                            *task_results_scoped[i * task_chunk_size + j]
                                                .write()
                                                .expect("could not get mutex") = Some(result);
                                        })
                                });
                                remaining_threads = remaining_threads.checked_sub(num_threads).unwrap();
                            }
                        });
                    });
                match Arc::try_unwrap(task_results) {
                    Ok(inner) => inner
                        .into_iter()
                        .map(|s| {
                            s.into_inner()
                                .expect("could not unwrap mutex")
                                .expect("result does not exist")
                        })
                        .collect(),
                    Err(_) => panic!("could not unwrap"),
                }
            } else {
                self.tasks.into_iter().map(|f| f()).collect()
            }
        }
        #[cfg(not(feature = "parallel"))]
        {
            self.tasks.into_iter().map(|f| f()).collect()
        }
    }
}

#[cfg(feature = "parallel")]
pub fn max_available_threads() -> usize {
    use aleo_std::Cpu;
    let rayon_threads = rayon::current_num_threads();
    match aleo_std::get_cpu() {
        Cpu::Intel | Cpu::Unknown => num_cpus::get_physical().min(rayon_threads),
        Cpu::AMD => rayon_threads,
    }
}

#[inline(always)]
pub fn execute_with_max_available_threads(f: impl FnOnce() + Send) {
    #[cfg(feature = "parallel")]
    {
        let num_threads = max_available_threads();
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap();

        pool.install(f);
    }
    #[cfg(not(feature = "parallel"))]
    {
        f();
    }
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
