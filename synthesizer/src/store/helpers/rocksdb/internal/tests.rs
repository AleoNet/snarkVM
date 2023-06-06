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

use crate::store::helpers::{
    rocksdb::{DataID, DataMap, Database, MapID, RocksDB, TestMap as TestMapID, PREFIX_LEN},
    Map,
    MapRead,
};
use console::{
    network::{Network, Testnet3},
    types::Scalar,
};
use snarkvm_utilities::{TestRng, Uniform};

use humansize::{format_size, BINARY};
use rayon::prelude::*;
use rocksdb::{Direction, IteratorMode};
use serial_test::serial;
use std::{borrow::Cow, fmt, time::Instant};

type TestMap = DataMap<u32, String>;

pub(crate) fn temp_dir() -> std::path::PathBuf {
    tempfile::tempdir().expect("Failed to open temporary directory").into_path()
}

// pub(crate) fn temp_file() -> std::path::PathBuf {
//     tempfile::NamedTempFile::new().expect("Failed to open temporary file").path().to_owned()
// }

#[test]
#[serial]
fn test_open() {
    let _storage = RocksDB::open_testing(temp_dir(), None).expect("Failed to open storage");
}

#[test]
#[serial]
fn test_open_map() {
    let _map = RocksDB::open_map_testing::<u32, String, _>(temp_dir(), None, MapID::Test(TestMapID::Test))
        .expect("Failed to open data map");
}

#[test]
#[serial]
fn test_insert_and_contains_key() {
    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    map.insert(123456789, "123456789".to_string()).expect("Failed to insert");
    assert!(map.contains_key_confirmed(&123456789).expect("Failed to call contains key"));
    assert!(!map.contains_key_confirmed(&000000000).expect("Failed to call contains key"));
}

#[test]
#[serial]
fn test_insert_and_get() {
    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    map.insert(123456789, "123456789".to_string()).expect("Failed to insert");
    assert_eq!(
        Some("123456789".to_string()),
        map.get_confirmed(&123456789).expect("Failed to get").map(|v| v.to_string())
    );

    assert_eq!(None, map.get_confirmed(&000000000).expect("Failed to get"));
}

#[test]
#[serial]
fn test_insert_and_remove() {
    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    map.insert(123456789, "123456789".to_string()).expect("Failed to insert");
    assert_eq!(
        map.get_confirmed(&123456789).expect("Failed to get").map(|v| v.to_string()),
        Some("123456789".to_string())
    );

    map.remove(&123456789).expect("Failed to remove");
    assert!(map.get_confirmed(&123456789).expect("Failed to get").is_none());
}

#[test]
#[serial]
fn test_insert_and_iter() {
    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    map.insert(123456789, "123456789".to_string()).expect("Failed to insert");

    let mut iter = map.iter_confirmed();
    assert_eq!(Some((123456789, "123456789".to_string())), iter.next().map(|(k, v)| (*k, v.to_string())));
    assert_eq!(None, iter.next());
}

#[test]
#[serial]
fn test_insert_and_keys() {
    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    map.insert(123456789, "123456789".to_string()).expect("Failed to insert");

    let mut keys = map.keys_confirmed();
    assert_eq!(Some(123456789), keys.next().map(|k| *k));
    assert_eq!(None, keys.next());
}

#[test]
#[serial]
fn test_insert_and_values() {
    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    map.insert(123456789, "123456789".to_string()).expect("Failed to insert");

    let mut values = map.values_confirmed();
    assert_eq!(Some("123456789".to_string()), values.next().map(|v| v.to_string()));
    assert_eq!(None, values.next());
}

#[test]
#[serial]
fn test_reopen() {
    let directory = temp_dir();
    {
        let map = RocksDB::open_map_testing(directory.clone(), None, MapID::Test(TestMapID::Test))
            .expect("Failed to open data map");
        map.insert(123456789, "123456789".to_string()).expect("Failed to insert");
    }
    {
        let map: TestMap =
            RocksDB::open_map_testing(directory, None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");
        match map.get_confirmed(&123456789).expect("Failed to get") {
            Some(Cow::Borrowed(value)) => assert_eq!(value.to_string(), "123456789".to_string()),
            Some(Cow::Owned(value)) => assert_eq!(value, "123456789".to_string()),
            None => panic!("Failed to get value"),
        }
    }
}

// #[test]
// #[serial]
// fn test_export_import() {
//     let file = temp_file();
//     {
//         let mut map = RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");
//
//         for i in 0..100 {
//             map.insert(i, i.to_string()).expect("Failed to insert");
//         }
//
//         storage.export(&file).expect("Failed to export storage");
//     }
//
//     let storage = RocksDB::open_temporary(temp_dir(), None).expect("Failed to open storage");
//     storage.import(&file).expect("Failed to import storage");
//
//     let map = storage.open_map::<u32, String>(MapID::Test(TestMapID::Test)).expect("Failed to open data map");
//
//     for i in 0..100 {
//         assert_eq!(map.get(&i).expect("Failed to get").map(|v| v.to_string()), Some(i.to_string()));
//     }
// }

#[test]
#[serial]
fn test_scalar_mul() {
    type CurrentNetwork = Testnet3;

    let rng = &mut TestRng::default();

    const ITERATIONS: u32 = 1_000_000u32;

    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    // Sample `ITERATION` random field elements to store.
    for i in 0..ITERATIONS {
        let value = Scalar::<CurrentNetwork>::rand(rng);
        map.insert(i, value).expect("Failed to insert");
    }

    let timer = std::time::Instant::now();

    // Execute scalar multiplication for each stored element.
    for value in map.values_confirmed() {
        let _group = CurrentNetwork::g_scalar_multiply(&*value);
    }

    let elapsed = timer.elapsed().as_secs();
    println!(" {ITERATIONS} Scalar Muls : {elapsed} s");
}

#[test]
#[serial]
fn test_iterator_ordering() {
    let map =
        RocksDB::open_map_testing(temp_dir(), None, MapID::Test(TestMapID::Test)).expect("Failed to open data map");

    // Insert values into the map.
    map.insert(5, "d".to_string()).expect("Failed to insert");
    map.insert(6, "c".to_string()).expect("Failed to insert");
    map.insert(7, "b".to_string()).expect("Failed to insert");
    map.insert(8, "a".to_string()).expect("Failed to insert");
    map.insert(1, "h".to_string()).expect("Failed to insert");
    map.insert(2, "g".to_string()).expect("Failed to insert");
    map.insert(3, "f".to_string()).expect("Failed to insert");
    map.insert(4, "e".to_string()).expect("Failed to insert");

    // Define the expected order of the iterator.
    let expected_order = vec![
        (1, "h".to_string()),
        (2, "g".to_string()),
        (3, "f".to_string()),
        (4, "e".to_string()),
        (5, "d".to_string()),
        (6, "c".to_string()),
        (7, "b".to_string()),
        (8, "a".to_string()),
    ];

    // Check that the order of the iterator is lexicographical.
    for ((k1, v1), (k2, v2)) in map.iter_confirmed().zip(expected_order.iter()) {
        assert_eq!(&*k1, k2);
        assert_eq!(&*v1, v2);
    }
}

#[test]
#[ignore = "This is intended as a means of manually inspecting some existing persistent storage."]
fn ledger_summary() {
    // Specify the storage- and prefix-related consts.
    const NETWORK_ID: u16 = 3;
    const DEV: Option<u16> = None;

    // The object containing stats related to a specific DataMap.
    #[derive(Default, Debug, Clone)]
    struct DataStats {
        num_records: usize,
        collective_key_size: usize,
        collective_value_size: usize,
    }
    impl fmt::Display for DataStats {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let num_records = self.num_records;
            let collective_key_size = self.collective_key_size;
            let collective_value_size = self.collective_value_size;

            let collective_size = format_size(collective_key_size + collective_value_size, BINARY);
            let keys_size = format_size(collective_key_size, BINARY);
            let values_size = format_size(collective_value_size, BINARY);

            let avg_key_size = collective_key_size.checked_div(num_records).unwrap_or_default();
            let avg_value_size = collective_value_size.checked_div(num_records).unwrap_or_default();
            let avg_key_size = format_size(avg_key_size, BINARY);
            let avg_value_size = format_size(avg_value_size, BINARY);

            write!(
                f,
                "{} records with a collective size of {} (keys: {}, values: {}); ",
                num_records, collective_size, keys_size, values_size
            )?;

            write!(f, "avg. key size: {}; avg. value size: {}", avg_key_size, avg_value_size)
        }
    }

    // Obtain the number of possible DataIDs.
    let data_id_count = enum_iterator::cardinality::<DataID>() as u16;
    println!("There are {data_id_count} DataIDs defined");

    // Make sure all of the variants are accounted for in the conversion impl.
    assert_eq!(data_id_count, 52, "The number of DataID variants has changed; adjust the TryFrom impl");

    // Start a timer.
    println!("Analyzing the database...");
    let start = Instant::now();

    // Open the database.
    let db = RocksDB::open(NETWORK_ID, DEV).unwrap();

    // Traverse the records belonging to each DataMap in parallel.
    let stats = (0..data_id_count)
        .into_par_iter()
        .map(|data_id| {
            let data_id_bytes = data_id.to_le_bytes();

            // Start iterating from the first record associated with the given DataID.
            let mut start = [0u8; PREFIX_LEN];
            start[..2].copy_from_slice(&NETWORK_ID.to_le_bytes());
            start[2..].copy_from_slice(&data_id_bytes);
            let iter = db.rocksdb.iterator(IteratorMode::From(&start, Direction::Forward));

            // Traverse all the applicable records.
            let mut data_stats = DataStats::default();
            for record in iter {
                let (key, value) = record.unwrap();

                // Once the DataID changes, there are no more relevant records.
                if &key[2..][..2] != &data_id_bytes {
                    break;
                }

                // Update the stats related to the given DataID.
                data_stats.num_records += 1;
                // Exclude the size of the key prefix.
                data_stats.collective_key_size += key.len() - PREFIX_LEN;
                data_stats.collective_value_size += value.len();
            }

            data_stats
        })
        .collect::<Vec<_>>();

    // Calculate global sums.
    let num_records = stats.iter().map(|stats| stats.num_records).sum::<usize>();
    let total_size = stats.iter().map(|s| s.collective_key_size + s.collective_value_size).sum::<usize>();
    println!("Processed the database in {}s.", start.elapsed().as_secs());
    println!("There are {} records, weighing {} in total.\n", num_records, format_size(total_size, BINARY));

    // Provide a summary for each DataID.
    for (data_id, data_stats) in enum_iterator::all::<DataID>().zip(stats) {
        println!("{:?}: {}", data_id, data_stats);
    }
}
