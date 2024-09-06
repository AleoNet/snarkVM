// Copyright 2024 Aleo Network Foundation
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

use crate::helpers::{
    rocksdb::{MapID, RocksDB, TestMap as TestMapID},
    Map,
    MapRead,
};
use console::{
    network::{MainnetV0, Network},
    prelude::{TestRng, Uniform},
    types::Scalar,
};

use serial_test::serial;

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
    type CurrentNetwork = MainnetV0;

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
