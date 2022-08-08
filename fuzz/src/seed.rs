use std::{env, fs};
use snarkvm::prelude::{Parser, Program};
use crate::CurrentNetwork;

pub fn seed() {
    let current_dir = env::current_dir().unwrap();


    for entry in fs::read_dir(current_dir.join("afl/seeds")).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.is_file() {
            let result = fs::read_to_string(path).unwrap();
            let program = Program::<CurrentNetwork>::parse(&result).unwrap();

        }


    }

}
