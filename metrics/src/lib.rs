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

#![forbid(unsafe_code)]

const GAUGE_NAMES: [&str; 1] = [committee::TOTAL_STAKE];

pub mod committee {
    pub const TOTAL_STAKE: &str = "snarkvm_ledger_committee_total_stake";
}

/// Registers all snarkVM metrics.
pub fn register_metrics() {
    for name in GAUGE_NAMES {
        register_gauge(name);
    }
}

/******** Counter ********/

/// Registers a counter with the given name.
pub fn register_counter(name: &'static str) {
    ::metrics::register_counter!(name);
}

/// Updates a counter with the given name to the given value.
///
/// Counters represent a single monotonic value, which means the value can only be incremented,
/// not decremented, and always starts out with an initial value of zero.
pub fn counter<V: Into<u64>>(name: &'static str, value: V) {
    ::metrics::counter!(name, value.into());
}

/// Increments a counter with the given name by one.
///
/// Counters represent a single monotonic value, which means the value can only be incremented,
/// not decremented, and always starts out with an initial value of zero.
pub fn increment_counter(name: &'static str) {
    ::metrics::increment_counter!(name);
}

/******** Gauge ********/

/// Registers a gauge with the given name.
pub fn register_gauge(name: &'static str) {
    ::metrics::register_gauge!(name);
}

/// Updates a gauge with the given name to the given value.
///
/// Gauges represent a single value that can go up or down over time,
/// and always starts out with an initial value of zero.
pub fn gauge<V: Into<f64>>(name: &'static str, value: V) {
    ::metrics::gauge!(name, value.into());
}

/// Increments a gauge with the given name by the given value.
///
/// Gauges represent a single value that can go up or down over time,
/// and always starts out with an initial value of zero.
pub fn increment_gauge<V: Into<f64>>(name: &'static str, value: V) {
    ::metrics::increment_gauge!(name, value.into());
}

/// Decrements a gauge with the given name by the given value.
///
/// Gauges represent a single value that can go up or down over time,
/// and always starts out with an initial value of zero.
pub fn decrement_gauge<V: Into<f64>>(name: &'static str, value: V) {
    ::metrics::decrement_gauge!(name, value.into());
}

/******** Histogram ********/

/// Registers a histogram with the given name.
pub fn register_histogram(name: &'static str) {
    ::metrics::register_histogram!(name);
}

/// Updates a histogram with the given name to the given value.
pub fn histogram<V: Into<f64>>(name: &'static str, value: V) {
    ::metrics::histogram!(name, value.into());
}
