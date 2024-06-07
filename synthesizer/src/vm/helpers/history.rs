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

use console::prelude::Serialize;

use aleo_std::{aleo_ledger_dir, StorageMode};

use anyhow::Result;
use serde_json;
use std::path::PathBuf;

/// Returns the path where a history directory may be stored.
pub fn history_directory_path(network: u16, storage_mode: StorageMode) -> PathBuf {
    const HISTORY_DIRECTORY_NAME: &str = "history";

    // Create the name of the history directory.
    let directory_name = match &storage_mode {
        StorageMode::Development(id) => format!(".{HISTORY_DIRECTORY_NAME}-{}-{}", network, id),
        StorageMode::Production | StorageMode::Custom(_) => format!("{HISTORY_DIRECTORY_NAME}-{}", network),
    };

    // Obtain the path to the ledger.
    let mut path = aleo_ledger_dir(network, storage_mode);
    // Go to the folder right above the ledger.
    path.pop();
    // Append the history directory's name.
    path.push(directory_name);

    path
}

#[derive(Copy, Clone)]
pub enum HistoryVariant {
    /// A `committee` mapping.
    Committee,
    /// A `bonded` mapping.
    Bonded,
    /// A `delegated` mapping.
    Delegated,
    /// An `unbonding` mapping.
    Unbonding,
}

impl HistoryVariant {
    /// Returns the name of the variant.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Committee => "committee",
            Self::Bonded => "bonded",
            Self::Delegated => "delegated",
            Self::Unbonding => "unbonding",
        }
    }
}

pub struct History {
    /// The path to the history directory.
    path: PathBuf,
}

impl History {
    /// Initializes a new instance of the history.
    pub fn new(network: u16, storage_mode: StorageMode) -> Self {
        Self { path: history_directory_path(network, storage_mode) }
    }

    /// Stores an entry into the history.
    pub fn store_entry<T>(&self, variant: HistoryVariant, height: u32, data: &T) -> Result<()>
    where
        T: Serialize + ?Sized,
    {
        // Get the path to the variant directory.
        let variant_path = self.variant_path(variant);
        // Create the variant directory if it does not exist.
        if !variant_path.exists() {
            std::fs::create_dir_all(&variant_path)?;
        }
        // Write the entry to the variant directory.
        let entry_path = variant_path.join(format!("{}-{height}.json", variant.name()));
        std::fs::write(entry_path, serde_json::to_string_pretty(data)?)?;

        Ok(())
    }

    /// Loads an entry from the history.
    pub fn load_entry(&self, variant: HistoryVariant, height: u32) -> Result<String> {
        // Get the path to the variant directory.
        let variant_path = self.variant_path(variant);
        // Read the entry from the variant directory.
        let entry_path = variant_path.join(format!("{}-{height}.json", variant.name()));
        let result = std::fs::read_to_string(entry_path)?;

        Ok(result)
    }

    /// Get the path to a variant directory.
    fn variant_path(&self, variant: HistoryVariant) -> PathBuf {
        self.path.join(variant.name())
    }
}
