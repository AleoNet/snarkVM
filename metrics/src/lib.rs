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

pub const GAUGE_NAMES: [&str; 1] = [committee::TOTAL_STAKE];

pub mod committee {
    pub const TOTAL_STAKE: &str = "snarkvm_ledger_committee_total_stake";
}

/// Registers all metrics.
pub fn register_metrics() {
    for name in GAUGE_NAMES {
        ::metrics::register_gauge!(name);
    }
}

/// Updates a gauge with the given name to the given value.
///
/// Gauges represent a single value that can go up or down over time,
/// and always starts out with an initial value of zero.
pub fn gauge<V: Into<f64>>(name: &'static str, value: V) {
    ::metrics::gauge!(name, value.into());
}
