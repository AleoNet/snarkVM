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

/// A helper macro to downcast a `$variable` to `$object<$network>`.
#[macro_export]
macro_rules! cast_ref {
    // Example: cast_ref!((foo.bar()) as Bar<Testnet3>)
    (($variable:expr) as $object:ident<$($traits:path),+>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($traits),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(bar as Bar<Testnet3>)
    ($variable:ident as $object:ident<$($traits:path),+>) => {{
        (&$variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($traits),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
    // Example: cast_ref!(&bar as Bar<Testnet3>)
    (&$variable:ident as $object:ident<$($traits:path),+>) => {{
        ($variable as &dyn std::any::Any)
            .downcast_ref::<$object<$($traits),+>>()
            .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($variable)))?
    }};
}

/// A helper macro to dedup the `Network` trait and `Aleo` trait and process its given logic.
#[macro_export]
macro_rules! process {
    // Example: process!(self, logic)
    ($self:ident, $logic:ident) => {{
        // Process the logic.
        match N::ID {
            console::network::Testnet3::ID => {
                // Cast the process.
                let process = (&$self.process as &dyn std::any::Any)
                    .downcast_ref::<Arc<RwLock<Process<console::network::Testnet3>>>>()
                    .ok_or_else(|| anyhow!("Failed to downcast {}", stringify!($self.process)))
                    .unwrap();

                $logic!(process.read(), console::network::Testnet3, circuit::AleoV0)
            }
            _ => Err(anyhow!("Unsupported VM configuration for network: {}", N::ID)),
        }
    }};
}
