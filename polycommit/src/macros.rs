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

#[macro_export]
macro_rules! execute_in_parallel {
    ($tasks:expr) => {{
        #[cfg(feature = "parallel")]
        {
            use itertools::Itertools;
            // At most 12 threads per task
            const THREADS_PER_TASK: usize = 12;
            let threads_per_task = if rayon::current_num_threads() > $tasks.len() * THREADS_PER_TASK {
                rayon::current_num_threads() / $tasks.len()
            } else {
                THREADS_PER_TASK.min(rayon::current_num_threads())
            };
            let task_chunk_size = rayon::current_num_threads() / threads_per_task
                + usize::from(rayon::current_num_threads() % threads_per_task != 0);

            if (threads_per_task as f64 / rayon::current_num_threads() as f64) < 1.0 {
                use std::sync::{Arc, RwLock};
                let mut task_results = Vec::with_capacity($tasks.len());
                for _ in 0..$tasks.len() {
                    task_results.push(RwLock::new(None));
                }
                let task_results = Arc::new(task_results);
                $tasks
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
                $tasks.into_iter().map(|f| f()).collect()
            }
        }
        #[cfg(not(feature = "parallel"))]
        {
            $tasks.into_iter().map(|f| f()).collect()
        }
    }};
}
