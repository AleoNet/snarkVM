// Copyright (C) 2019-2023 Aleo Systems Inc.
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

pub mod credits;
pub use credits::*;

pub mod deploy;
pub use deploy::*;

pub mod dummy;
pub use dummy::*;

pub mod get;
pub use get::*;

pub mod get_or_init;
pub use get_or_init::*;

pub mod set;
pub use set::*;

use crate::utilities::{Benchmark, Workload};

use console::network::Testnet3;

// WARNING:
// - Deleting or modifying ANY of these workloads will require to regenerate them from scratch.
// - This will delete the existing saved workload and may take hours to complete.
// - To create new workloads, it is advised to create a new function with a unique name for the workload.

/// A helper function to create a workload that benches executions individually.
pub fn one_execution_workload(config: &[usize]) -> Workload {
    // Initialize the workload.
    let mut workload = Workload::new("one_execution".to_string(), vec![]).unwrap();
    for num_commands in config {
        workload.add(Box::new(StaticGet::new(1, *num_commands, 1, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticGetOrInit::new(1, *num_commands, 1, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticSet::new(1, *num_commands, 1, 1)) as Box<dyn Benchmark<Testnet3>>);
    }
    workload.add(Box::new(MintPublic::new(1)) as Box<dyn Benchmark<Testnet3>>);
    workload.add(Box::new(TransferPrivateToPublic::new(1)) as Box<dyn Benchmark<Testnet3>>);
    workload.add(Box::new(TransferPublic::new(1)) as Box<dyn Benchmark<Testnet3>>);
    workload.add(Box::new(TransferPublicToPrivate::new(1)) as Box<dyn Benchmark<Testnet3>>);

    workload
}

/// A helper function to create a workload that benches multiple executions of the same program.
pub fn multiple_executions_workload(config: &[usize], max_commands: usize) -> Workload {
    // Initialize the workloads.
    let mut workload = Workload::new("multiple_executions".to_string(), vec![]).unwrap();
    for num_executions in config {
        workload.add(Box::new(StaticGet::new(1, max_commands, *num_executions, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload
            .add(Box::new(StaticGetOrInit::new(1, max_commands, *num_executions, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticSet::new(1, max_commands, *num_executions, 1)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(MintPublic::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(TransferPrivateToPublic::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(TransferPublic::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(TransferPublicToPrivate::new(*num_executions)) as Box<dyn Benchmark<Testnet3>>);
    }

    workload
}

/// A helper function to create a workload that benches multiple executions of the multiple programs.
pub fn multiple_executions_multiple_programs_workload(
    config: &[usize],
    max_commands: usize,
    max_executions: usize,
) -> Workload {
    // Initialize the workloads.
    let mut workload = Workload::new("multiple_executions_multiple_programs".to_string(), vec![]).unwrap();
    for num_programs in config {
        workload
            .add(Box::new(StaticGet::new(1, max_commands, max_executions, *num_programs))
                as Box<dyn Benchmark<Testnet3>>);
        workload.add(Box::new(StaticGetOrInit::new(1, max_commands, max_executions, *num_programs))
            as Box<dyn Benchmark<Testnet3>>);
        workload
            .add(Box::new(StaticSet::new(1, max_commands, max_executions, *num_programs))
                as Box<dyn Benchmark<Testnet3>>);
    }

    workload
}

/// A helper function to create a workload that benches the deployment of a single program.
pub fn single_deployment_workload(config: &[usize]) -> Workload {
    // Initialize the workloads.
    let mut workload = Workload::new("single_deployment".to_string(), vec![]).unwrap();
    for num_mappings in config {
        workload.add(Box::new(DeploySingle::new(*num_mappings)) as Box<dyn Benchmark<Testnet3>>);
    }
    workload
}

/// A helper function to create a workload that benches the deployment of multiple programs.
pub fn multiple_deployments_workload(config: &[usize], max_mappings: usize) -> Workload {
    // Initialize the workloads.
    let mut workload = Workload::new("multiple_deployments".to_string(), vec![]).unwrap();
    for num_deployments in config {
        workload.add(Box::new(DeployMultiple::new(max_mappings, *num_deployments)) as Box<dyn Benchmark<Testnet3>>);
    }
    workload
}
