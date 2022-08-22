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


use clap::{self, StructOpt, Subcommand};
use core::time::Duration;
use std::{env, net::SocketAddr, panic, path::PathBuf};
use std::process::abort;
use arbitrary::{Arbitrary, Unstructured};

use libafl::{
    bolts::{
        core_affinity::Cores,
        current_nanos,
        launcher::Launcher,
        rands::StdRand,
        shmem::{ShMemProvider, StdShMemProvider},
        tuples::{tuple_list, Merge},
        AsSlice,
    },
    corpus::{Corpus, InMemoryCorpus, OnDiskCorpus},
    events::EventConfig,
    executors::{inprocess::InProcessExecutor, ExitKind, TimeoutExecutor},
    feedback_or, feedback_or_fast,
    feedbacks::{CrashFeedback, MaxMapFeedback, TimeFeedback, TimeoutFeedback},
    fuzzer::{Fuzzer, StdFuzzer},
    inputs::{BytesInput, HasTargetBytes},
    monitors::{MultiMonitor, OnDiskTOMLMonitor},
    mutators::scheduled::{havoc_mutations, tokens_mutations, StdScheduledMutator},
    mutators::token_mutations::Tokens,
    observers::{HitcountsMapObserver, StdMapObserver, TimeObserver},
    schedulers::{IndexesLenTimeMinimizerScheduler, QueueScheduler},
    stages::mutational::StdMutationalStage,
    state::{HasCorpus, HasMetadata, StdState},
    Error,
};
use libafl::corpus::CachedOnDiskCorpus;
use libafl::corpus::ondisk::OnDiskMetadataFormat;

use libafl_targets::{EDGES_MAP, MAX_EDGES_NUM};
use snarkvm::prelude::{Environment, Parser, Program};
use snarkvm_fuzz::harness::{harness, init_vm};
use crate::cli::{Cli, Commands};

/// Parse a millis string to a [`Duration`]. Used for arg parsing.
fn timeout_from_millis_str(time: &str) -> Result<Duration, Error> {
    Ok(Duration::from_millis(time.parse()?))
}

#[derive(Debug, StructOpt)]
pub struct FuzzCli {
    #[clap(
    short,
    long,
    parse(try_from_str = Cores::from_cmdline),
    help = "Spawn a client in each of the provided cores. Broker runs in the 0th core. 'all' to select all available cores. 'none' to run a client without binding to any core. eg: '1,2-4,6' selects the cores 1,2,3,4,6.",
    name = "CORES"
    )]
    cores: Cores,

    #[clap(
    short = 'p',
    long,
    help = "Choose the broker TCP port, default is 1337",
    name = "PORT",
    default_value = "1337"
    )]
    broker_port: u16,

    #[clap(
    parse(try_from_str),
    short = 'a',
    long,
    help = "Specify a remote broker",
    name = "REMOTE"
    )]
    remote_broker_addr: Option<SocketAddr>,

    #[clap(
    parse(try_from_str),
    short,
    long,
    help = "Set an initial corpus directory",
    name = "INPUT"
    )]
    input: Vec<PathBuf>,

    #[clap(
    short,
    long,
    parse(try_from_str),
    help = "Set the output directory, default is ./objective",
    name = "OUTPUT",
    default_value = "./objective"
    )]
    output: PathBuf,

    #[clap(
    short = 's',
    long,
    parse(try_from_str),
    help = "Set the  corpus directory, default is ./corpus",
    name = "OUTPUT",
    default_value = "./corpus"
    )]
    corpus: PathBuf,

    #[clap(
    parse(try_from_str = timeout_from_millis_str),
    short,
    long,
    help = "Set the exeucution timeout in milliseconds, default is 10000",
    name = "TIMEOUT",
    default_value = "20000"
    )]
    timeout: Duration,
    /*
    /// This fuzzer has hard-coded tokens
    #[clap(
        parse(from_os_str),
        short = "x",
        long,
        help = "Feed the fuzzer with an user-specified list of tokens (often called \"dictionary\"",
        name = "TOKENS",
        multiple = true
    )]
    tokens: Vec<PathBuf>,
    */
}

impl FuzzCli {
    pub fn fuzz(self) {
        // Registry the metadata types used in this fuzzer
        // Needed only on no_std
        //RegistryBuilder::register::<Tokens>();

        let broker_port = self.broker_port;
        let cores = self.cores.clone();

        println!(
            "Init vm",
        );

        init_vm();

        println!(
            "Workdir: {:?}",
            env::current_dir().unwrap().to_string_lossy().to_string()
        );

        let shmem_provider = StdShMemProvider::new().expect("Failed to init shared memory");

        let monitor = OnDiskTOMLMonitor::new(
            "./fuzzer_stats.toml",
            MultiMonitor::new(|s| println!("{}", s)),
        );

        let mut run_client = |state: Option<_>, mut restarting_mgr, _core_id| {
            // Create an observation channel using the coverage map
            let edges = unsafe { &mut EDGES_MAP[0..MAX_EDGES_NUM] };
            let edges_observer = HitcountsMapObserver::new(StdMapObserver::new("edges", edges));

            // Create an observation channel to keep track of the execution time
            let time_observer = TimeObserver::new("time");

            // Feedback to rate the interestingness of an input
            // This one is composed by two Feedbacks in OR
            let mut feedback = feedback_or!(
                // New maximization map feedback linked to the edges observer and the feedback state
                MaxMapFeedback::new_tracking(&edges_observer, true, false),
                // Time feedback, this one does not need a feedback state
                TimeFeedback::new_with_observer(&time_observer)
            );

            // A feedback to choose if an input is a solution or not
            let mut objective = feedback_or_fast!(CrashFeedback::new(), TimeoutFeedback::new());

            // If not restarting, create a State from scratch
            let mut state = state.unwrap_or_else(|| {
                StdState::new(
                    // RNG
                    StdRand::with_seed(current_nanos()),
                    // Corpus that will be evolved
                    CachedOnDiskCorpus::new(self.corpus.clone(), 10000).unwrap(),
                    // Corpus in which we store solutions (crashes in this example),
                    // on disk so the user can get them after stopping the fuzzer
                    OnDiskCorpus::new_save_meta(
                        self.output.clone(),
                        Some(OnDiskMetadataFormat::JsonPretty),
                    ).unwrap(),
                    // States of the feedbacks.
                    // The feedbacks can report the data that should persist in the State.
                    &mut feedback,
                    // Same for objective feedbacks
                    &mut objective,
                )
                    .unwrap()
            });

            println!("We're a client, let's fuzz :)");

            // Setup a basic mutator with a mutational stage
            let mutator = StdScheduledMutator::new(havoc_mutations());
            let mut stages = tuple_list!(StdMutationalStage::new(mutator));

            // A minimization+queue policy to get testcasess from the corpus
            let scheduler = IndexesLenTimeMinimizerScheduler::new(QueueScheduler::new());

            // A fuzzer with feedbacks and a corpus scheduler
            let mut fuzzer = StdFuzzer::new(scheduler, feedback, objective);

            // The wrapped harness function, calling out to the LLVM-style harness
            let mut harness = |input: &BytesInput| {
                let target = input.target_bytes();
                let buf = target.as_slice();
                harness(buf);
                // Not sure whether we can skip here somehow
                ExitKind::Ok
            };

            // Create the executor for an in-process function with one observer for edge coverage and one for the execution time
            let mut executor = TimeoutExecutor::new(
                InProcessExecutor::new(
                    &mut harness,
                    tuple_list!(edges_observer, time_observer),
                    &mut fuzzer,
                    &mut state,
                    &mut restarting_mgr,
                )?,
                // 10 seconds timeout
                self.timeout,
            );

            // In case the corpus is empty (on first run), reset
            if state.corpus().count() < 1 {
                state
                    .load_initial_inputs(&mut fuzzer, &mut executor, &mut restarting_mgr, &self.input)
                    .unwrap_or_else(|_| panic!("Failed to load initial corpus at {:?}", &self.input));
                println!("We imported {} inputs from disk.", state.corpus().count());
            }

            // LibAFL has a panic hook. We are allowing some panics though.
            panic::set_hook(Box::new(|panic_info| {}));

            fuzzer.fuzz_loop(&mut stages, &mut executor, &mut state, &mut restarting_mgr)?;
            Ok(())
        };

        match Launcher::builder()
            .shmem_provider(shmem_provider)
            .configuration(EventConfig::from_name("default"))
            .monitor(monitor)
            .run_client(&mut run_client)
            .cores(&cores)
            .broker_port(broker_port)
            .remote_broker_addr(self.remote_broker_addr)
            .stdout_file(Some("/dev/null"))
            .build()
            .launch()
        {
            Ok(()) => (),
            Err(Error::ShuttingDown) => println!("Fuzzing stopped by user. Good bye."),
            Err(err) => panic!("Failed to run launcher: {:?}", err),
        }
    }
}

