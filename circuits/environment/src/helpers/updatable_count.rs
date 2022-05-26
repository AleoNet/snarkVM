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

use crate::{Constant, Constraints, Measurement, Private, Public};

use core::fmt::Debug;
use once_cell::sync::{Lazy, OnceCell};
use std::{
    cmp::Ordering,
    collections::{BTreeSet, HashMap},
    env,
    fmt::Display,
    fs,
    ops::Range,
    path::{Path, PathBuf},
    sync::Mutex,
};

static FILES: Lazy<Mutex<HashMap<&'static str, FileUpdates>>> = Lazy::new(Default::default);
static WORKSPACE_ROOT: OnceCell<PathBuf> = OnceCell::new();

#[macro_export]
macro_rules! count_is {
    ($num_constants:literal, $num_public:literal, $num_private:literal, $num_constraints:literal) => {
        $crate::UpdatableCount {
            constant: $crate::Measurement::Exact($num_constants),
            public: $crate::Measurement::Exact($num_public),
            private: $crate::Measurement::Exact($num_private),
            constraints: $crate::Measurement::Exact($num_constraints),
            file: file!(),
            line: line!(),
            column: column!(),
        }
    };
}

#[macro_export]
macro_rules! count_less_than {
    ($num_constants:literal, $num_public:literal, $num_private:literal, $num_constraints:literal) => {
        $crate::UpdatableCount {
            constant: $crate::Measurement::UpperBound($num_constants),
            public: $crate::Measurement::UpperBound($num_public),
            private: $crate::Measurement::UpperBound($num_private),
            constraints: $crate::Measurement::UpperBound($num_constraints),
            file: file!(),
            line: line!(),
            column: column!(),
        }
    };
}

/// A helper struct for tracking the number of constants, public inputs, private inputs, and constraints.
#[derive(Copy, Clone, Debug)]
pub struct UpdatableCount {
    pub constant: Constant,
    pub public: Public,
    pub private: Private,
    pub constraints: Constraints,
    #[doc(hidden)]
    pub file: &'static str,
    #[doc(hidden)]
    pub line: u32,
    #[doc(hidden)]
    pub column: u32,
}

impl Display for UpdatableCount {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Constants: {}, Public: {}, Private: {}, Constraints: {}",
            self.constant, self.public, self.private, self.constraints
        )
    }
}

impl UpdatableCount {
    pub fn matches(&self, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) -> bool {
        self.constant.matches(num_constants)
            && self.public.matches(num_public)
            && self.private.matches(num_private)
            && self.constraints.matches(num_constraints)
    }

    /// If all constituent metrics match, do nothing.
    /// If all consituent metrics do not match:
    ///    - If the update condition is satisfied, then update the macro invocation that constructed this `UpdatableCount`.
    ///    - Otherwise, panic.
    pub fn assert_matches(&self, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        if !self.matches(num_constants, num_public, num_private, num_constraints) {
            let mut files = FILES.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            match env::var("UPDATE_COUNT") {
                Ok(query_string) if self.file.contains(&query_string) => {
                    // TODO: Provide metrics on update.
                    files.entry(self.file).or_insert_with(|| FileUpdates::new(self)).update_count(
                        self,
                        num_constants,
                        num_public,
                        num_private,
                        num_constraints,
                    );
                }
                _ => {
                    println!(
                        "\n
\x1b[1m\x1b[91merror\x1b[97m: Count does not match\x1b[0m
   \x1b[1m\x1b[34m-->\x1b[0m {}:{}:{}
\x1b[1mExpected\x1b[0m:
----
{}
----
\x1b[1mActual\x1b[0m:
----
Constants: {}, Public: {}, Private: {}, Constraints: {}
----
",
                        self.file,
                        self.line,
                        self.column,
                        self,
                        num_constants,
                        num_public,
                        num_private,
                        num_constraints,
                    );
                    // Use resume_unwind instead of panic!() to prevent a backtrace, which is unnecessary noise.
                    snarkvm_utilities::panic::resume_unwind(Box::new(()));
                }
            }
        }
    }

    /// Given a string containing the contents of a file, `locate` returns a range delimiting the arguments.
    /// to the macro invocation that constructed this `UpdatableCount`.
    /// The beginning of the range corresponds to the opening parenthesis of the macro invocation.
    /// The end of the range corresponds to the closing parenthesis of the macro invocation.
    /// ```ignore
    ///              count_is!(0, 1, 2, 3)
    /// ```                   ^          ^
    ///    starting_byte_offset          ending_byte_offset
    ///
    /// Note: This function must always invoked with the file contents of the same file as the macro invocation.
    fn locate(&self, file: &str) -> Range<usize> {
        // `line_start` is the absolute byte offset from the beginning of the file to the beginning of the current line.
        let mut line_start = 0;
        let mut starting_byte_offset = None;
        let mut ending_byte_offset = None;
        for (i, line) in LinesWithEnds::from(file).enumerate() {
            if i == self.line as usize - 1 {
                // Seek past the exclamation point, then skip any whitespace and the macro delimiter to get to the opening parentheses.
                let mut argument_character_indices = line.char_indices().skip((self.column - 1).try_into().unwrap())
                    .skip_while(|&(_, c)| c != '!') // Skip up to the exclamation point.
                    .skip(1) // Skip `!`.
                    .skip_while(|(_, c)| c.is_whitespace()); // Skip any whitespace.

                starting_byte_offset = Some(
                    line_start
                        + argument_character_indices
                            .next()
                            .expect("Could not find the beginning of the macro invocation.")
                            .0,
                );
            }

            if starting_byte_offset.is_some() {
                // At this point, we have found the opening parentheses, so we continue to skip all characters until the closing parentheses.
                match line.char_indices().find(|&(_, c)| c == ')') {
                    None => (), // Do nothing. This means that the closing parentheses was not found on the same line as the opening parentheses.
                    Some((offset, _)) => {
                        // Note that the `+ 1` is to account for the fact that `std::ops::Range` is exclusive on the upper bound.
                        ending_byte_offset = Some(line_start + offset + 1);
                        break;
                    }
                }
            }
            line_start += line.len();
        }

        Range {
            start: starting_byte_offset.expect("Could not find the beginning of the macro invocation."),
            end: ending_byte_offset.expect("Could not find the ending of the macro invocation."),
        }
    }

    // TODO: Consider renaming.
    /// Computes the ratio of the number of constants, public, private, and constraints that `other` has compared to `self`.
    pub fn diff(&self, other: &Self) -> (f64, f64, f64, f64) {
        let compute_diff = |self_measurement, other_measurement| {
            match (self_measurement, other_measurement) {
                (Measurement::Exact(self_value), Measurement::Exact(other_value))
                | (Measurement::UpperBound(self_value), Measurement::UpperBound(other_value)) => {
                    other_value as f64 / self_value as f64
                }
                _ => panic!("Cannot compute difference for `Measurement::Range` or if both measurements are of different types."),
            }
        };
        (compute_diff(self.constant, other.constant), compute_diff(self.public, other.public), compute_diff(self.private, other.private), compute_diff(self.constraints, other.constraints))
    }

    fn dummy(constant: Constant, public: Public, private: Private, constraints: Constraints) -> Self {
        Self {
            constant,
            public,
            private,
            constraints,
            file: Default::default(),
            line: Default::default(),
            column: Default::default(),
        }
    }

    fn as_argument_string(&self) -> String {
        let generate_arg = |measurement| match measurement {
            Measurement::Exact(value) => value,
            Measurement::UpperBound(bound) => bound,
            Measurement::Range(..) => panic!(
                "Cannot create an argument string from an `UpdatableCount` that contains a `Measurement::Range`."
            ),
        };
        format!(
            "({}, {}, {}, {})",
            generate_arg(self.constant),
            generate_arg(self.public),
            generate_arg(self.private),
            generate_arg(self.constraints)
        )
    }
}

/// This struct is used to track updates to the `UpdatableCount`s in a file.
/// It is used to ensure that the updates are written to the appropriate location in the file as the file is modified.
struct FileUpdates {
    absolute_path: PathBuf,
    original_text: String,
    modified_text: String,
    /// An ordered set of `Update`s.
    /// We assume that all `Updates` are made to disjoint ranges in the original file.
    /// This assumption is valid since invocations of `count_is` and `count_less_than` cannot be nested.
    updates: BTreeSet<Update>,
}

impl FileUpdates {
    /// Initializes a new instance of `FileUpdates`.
    /// This function will read the contents of the file at the specified path and store it in the `original_text` field.
    /// This function will also initialize the `updates` field to an empty vector.
    fn new(count: &UpdatableCount) -> Self {
        let path = Path::new(count.file);
        let absolute_path = match path.is_absolute() {
            true => path.to_owned(),
            false => {
                WORKSPACE_ROOT
                    .get_or_try_init(|| {
                        // Heuristic, see https://github.com/rust-lang/cargo/issues/3946
                        let workspace_root = Path::new(&env!("CARGO_MANIFEST_DIR"))
                            .ancestors()
                            .filter(|it| it.join("Cargo.toml").exists())
                            .last()
                            .unwrap()
                            .to_path_buf();

                        Ok(workspace_root)
                    })
                    .unwrap_or_else(|_: env::VarError| {
                        panic!("No CARGO_MANIFEST_DIR env var and the path is relative: {}", path.display())
                    })
                    .join(path)
            }
        };
        let original_text = fs::read_to_string(&absolute_path).unwrap();
        let modified_text = original_text.clone();
        let updates = Default::default();
        Self { absolute_path, original_text, modified_text, updates }
    }

    /// This function will update the `modified_text` field with the new text that is being inserted.
    /// The resulting `modified_text` is written to the file at the specified path.
    fn update_count(
        &mut self,
        count: &UpdatableCount,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        // Get the location of arguments in the macro invocation.
        let range = count.locate(&self.original_text);

        let mut new_range = range.clone();
        let mut update_with_same_start = None;

        // Shift the range to account for changes made to the original file.
        for previous_update in &self.updates {
            let amount_deleted = previous_update.end - previous_update.start;
            let amount_inserted = previous_update.argument_string.len();

            if previous_update.start < range.start {
                // If an update was made in a location preceding the range in the original file, we need to shift the range by the length of the text that was changed.
                new_range.start = new_range.start - amount_deleted + amount_inserted;
                new_range.end = new_range.end - amount_deleted + amount_inserted;
            } else if previous_update.start == range.start {
                // If an update was made at the same location as the range in the original file, we need to shift the end of the range by the amount of text that was changed.
                new_range.end = new_range.end - amount_deleted + amount_inserted;
                update_with_same_start = Some(previous_update);
            }
        }

        // If there an update to the original text has been made, then check if the counts satisfies the updated `Count`.
        // If so, then there is no need to write to update the file and we can return early.
        if let Some(update) = update_with_same_start {
            if update.count.matches(num_constants, num_public, num_private, num_constraints) {
                return;
            }
        }

        // Construct the new update.
        let new_update = match update_with_same_start {
            None => Update::new(&range, count, num_constants, num_public, num_private, num_constraints),
            Some(update) => Update::new(&range, &update.count, num_constants, num_public, num_private, num_constraints),
        };

        // Apply the update.
        self.modified_text.replace_range(new_range, &new_update.argument_string);

        // Add the new update to the set of updates.
        self.updates.replace(new_update);

        // Update the original file with the modified text.
        fs::write(&self.absolute_path, &self.modified_text).unwrap()
    }
}

/// Helper struct to keep track of updates to the original file.
#[derive(Debug)]
struct Update {
    /// Starting location in the original file.
    start: usize,
    /// Ending location in the original file.
    end: usize,
    /// A dummy count with the new `Measurement`s.
    count: UpdatableCount,
    /// A string representation of `count`.
    argument_string: String,
}

impl Update {
    fn new(
        range: &Range<usize>,
        old_count: &UpdatableCount,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Self {
        let generate_new_measurement = |measurement: Measurement<u64>, num: u64| match measurement {
            Measurement::Exact(..) => Measurement::Exact(num),
            Measurement::Range(..) => panic!("UpdatableCount does not support ranges."),
            Measurement::UpperBound(bound) => Measurement::UpperBound(std::cmp::max(num, bound)),
        };
        let count = UpdatableCount::dummy(
            generate_new_measurement(old_count.constant, num_constants),
            generate_new_measurement(old_count.public, num_public),
            generate_new_measurement(old_count.private, num_private),
            generate_new_measurement(old_count.constraints, num_constraints),
        );
        Self { start: range.start, end: range.end, count, argument_string: count.as_argument_string() }
    }
}

impl PartialEq for Update {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start
    }
}
impl Eq for Update {}
impl PartialOrd for Update {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Update {
    fn cmp(&self, other: &Self) -> Ordering {
        self.start.cmp(&other.start)
    }
}

/// A struct that provides an iterator over the lines in a string, while preserving the original line endings.
// This is necessary as `str::lines` does not preserve the original line endings.
struct LinesWithEnds<'a> {
    text: &'a str,
}

impl<'a> Iterator for LinesWithEnds<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        match self.text.is_empty() {
            true => None,
            false => {
                let idx = self.text.find('\n').map_or(self.text.len(), |it| it + 1);
                let (res, next) = self.text.split_at(idx);
                self.text = next;
                Some(res)
            }
        }
    }
}

impl<'a> From<&'a str> for LinesWithEnds<'a> {
    fn from(text: &'a str) -> Self {
        LinesWithEnds { text }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use snarkvm_utilities::{test_rng, UniformRand};

    use serial_test::serial;
    use std::env;

    const ITERATIONS: u64 = 1024;

    #[test]
    fn check_position() {
        let count = count_is!(0, 0, 0, 0);
        assert_eq!(count.file, "circuits/environment/src/helpers/updatable_count.rs");
        assert_eq!(count.line, 417);
        assert_eq!(count.column, 21);
    }

    #[test]
    #[serial]
    fn check_count_passes() {
        let original_count = count_is!(1, 2, 3, 4);
        let num_constants = 1;
        let num_public = 2;
        let num_private = 3;
        let num_inputs = 4;
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);
    }

    #[test]
    #[serial]
    #[should_panic]
    fn check_count_fails() {
        let original_count = count_is!(1, 2, 3, 4);
        let num_constants = 5;
        let num_public = 6;
        let num_private = 7;
        let num_inputs = 8;

        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);
    }

    #[test]
    #[serial]
    #[should_panic]
    fn check_count_does_not_update_if_env_var_is_not_set_correctly() {
        let original_count = count_is!(1, 2, 3, 4);
        let num_constants = 5;
        let num_public = 6;
        let num_private = 7;
        let num_inputs = 8;

        // Set the environment variable to update the file.
        env::set_var("UPDATE_COUNT", "1");

        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        env::remove_var("UPDATE_COUNT");
    }

    #[test]
    #[serial]
    fn check_count_updates_correctly() {
        // `original_count` is originally `count_is!(1, 2, 3, 4)`. Replace `original_count` to demonstrate replacement.
        let original_count = count_is!(11, 12, 13, 14);
        let num_constants = 11;
        let num_public = 12;
        let num_private = 13;
        let num_inputs = 14;

        // Set the environment variable to update the file.
        env::set_var("UPDATE_COUNT", "updatable_count.rs");

        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        env::remove_var("UPDATE_COUNT");
    }

    #[test]
    #[serial]
    fn check_count_updates_correctly_multiple_times() {
        // `original_count` is originally `count_is!(1, 2, 3, 4)`. Replace `original_count` to demonstrate replacement.
        let original_count = count_is!(17, 18, 19, 20);

        env::set_var("UPDATE_COUNT", "updatable_count.rs");

        let (num_constants, num_public, num_private, num_inputs) = (5, 6, 7, 8);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        let (num_constants, num_public, num_private, num_inputs) = (9, 10, 11, 12);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        let (num_constants, num_public, num_private, num_inputs) = (13, 14, 15, 16);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        let (num_constants, num_public, num_private, num_inputs) = (17, 18, 19, 20);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        env::remove_var("UPDATE_COUNT");
    }

    #[test]
    #[serial]
    fn check_count_less_than_selects_maximum() {
        // `original_count` is initially `count_less_than!(1, 2, 3, 4)`.
        // After counts are updated, `original_count` is `count_less_than!(17, 18, 19, 20)`.
        // In other words, original_count is updated to be the maximum of the original and updated counts.
        let original_count = count_less_than!(17, 18, 19, 20);

        // Set the environment variable to update the file.
        env::set_var("UPDATE_COUNT", "updatable_count.rs");

        let (num_constants, num_public, num_private, num_inputs) = (5, 18, 7, 8);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        let (num_constants, num_public, num_private, num_inputs) = (17, 10, 11, 12);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        let (num_constants, num_public, num_private, num_inputs) = (13, 6, 19, 16);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        let (num_constants, num_public, num_private, num_inputs) = (9, 18, 15, 20);
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        env::remove_var("UPDATE_COUNT");
    }
}
