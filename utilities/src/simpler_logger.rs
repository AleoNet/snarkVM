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

//! A logger that prints to stdout and stderr.
//!
//! All records with a level of `Info` or higher are printed as-is to stdout, and all
//! records with a level of `Warn` or Lower are printed to stderr.
//!
//! # Example
//! ```rust
//! use snarkvm_utilities::simpler_logger::SimplerLogger;
//!
//! SimplerLogger::new().init().unwrap();
//! log::trace!("trace"); // -> stdout
//! log::debug!("debug"); // -> stdout
//! log::info!("info"); // -> stdout
//! log::warn!("warn"); // -> stderr
//! log::error!("error"); // -> stderr
//! ```
//!
use log::{Log, Metadata, Record};

pub struct SimplerLogger;

impl SimplerLogger {
    pub fn new() -> SimplerLogger {
        SimplerLogger {}
    }

    pub fn init(self) -> Result<(), log::SetLoggerError> {
        log::set_boxed_logger(Box::new(self))?;
        log::set_max_level(log::LevelFilter::Trace);
        Ok(())
    }
}

impl Default for SimplerLogger {
    fn default() -> Self {
        Self::new()
    }
}

impl Log for SimplerLogger {
    fn log(&self, message: &Record) {
        // Confusingly, Level::Error is `1`, and Level::Trace is `5`.
        if message.level() >= log::Level::Info {
            println!("{}", message.args());
        } else if message.level() < log::Level::Info {
            eprintln!("{}", message.args());
        }
    }

    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn flush(&self) {}
}
