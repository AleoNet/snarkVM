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

use crate::{Constant, Constraints, Private, Public};

use core::fmt::Debug;
use once_cell::sync::{Lazy, OnceCell};
use std::{
    collections::HashMap,
    env,
    fs,
    ops::Range,
    path::{Path, PathBuf},
    sync::Mutex,
};

static FILES: Lazy<Mutex<HashMap<&'static str, FileUpdates>>> = Lazy::new(Default::default);

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

/// A helper struct for tracking the number of constants, public inputs, private inputs, and constraints.
#[derive(Copy, Clone, Debug)]
pub struct UpdatableCount {
    constant: Constant,
    public: Public,
    private: Private,
    constraints: Constraints,
    #[doc(hidden)]
    file: &'static str,
    #[doc(hidden)]
    pub line: u32,
    #[doc(hidden)]
    pub column: u32,
}

impl UpdatableCount {
    /// If all constituent metrics match, do nothing.
    /// If all consituent metrics do not match:
    ///    - If the update condition is satisfied, then update the macro invocation that constructed this `UpdatableCount`.
    ///    - Otherwise, panic.
    pub fn assert_matches(&self, num_constants: u64, num_public: u64, num_private: u64, num_constraints: u64) {
        if !(self.constant.matches(num_constants)
            && self.public.matches(num_public)
            && self.private.matches(num_private)
            && self.constraints.matches(num_constraints))
        {
            let mut files = FILES.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            // TODO: Currently, we always update the count. Fix to be selective.
            if update_counts() {
                // TODO: Provide metrics on update.
                files.entry(self.file).or_insert_with(|| FileUpdates::new(self)).update_count(
                    self,
                    num_constants,
                    num_public,
                    num_private,
                    num_constraints,
                );
            } else {
                // TODO: Better panics.
                println!(
                    "\n
\x1b[1m\x1b[91merror\x1b[97m: expect test failed\x1b[0m
   \x1b[1m\x1b[34m-->\x1b[0m {}:{}:{}
\x1b[1mExpected\x1b[0m:
----
{:?}
----
\x1b[1mActual\x1b[0m:
----
{:?}
----
",
                    self.file,
                    self.line,
                    self.column,
                    (num_constants, num_public, num_private, num_constraints),
                    self,
                );
                // Use resume_unwind instead of panic!() to prevent a backtrace, which is unnecessary noise.
                snarkvm_utilities::panic::resume_unwind(Box::new(()));
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
}

struct FileUpdates {
    path: PathBuf,
    original_text: String,
    modified_text: String,
    updates: Vec<(Range<usize>, usize)>,
}

impl FileUpdates {
    fn new(count: &UpdatableCount) -> Self {
        let path = to_abs_ws_path(Path::new(count.file));
        let original_text = fs::read_to_string(&path).unwrap();
        let modified_text = original_text.clone();
        let updates = Vec::new();
        Self { path, original_text, modified_text, updates }
    }

    fn update_count(
        &mut self,
        count: &UpdatableCount,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) {
        // Get the location of arguments in the macro invocation.
        let mut range = count.locate(&self.original_text);

        // Format a string with the new counts.
        let argument_string = format!("({}, {}, {}, {})", num_constants, num_public, num_private, num_constraints);

        // Update the modified text with the desired modification.
        self.updates.push((range.clone(), argument_string.len()));
        self.updates.sort_by_key(|(delete, _insert)| delete.start);

        let (delete, insert) = self
            .updates
            .iter()
            .take_while(|(delete, _)| delete.start < range.start)
            .map(|(delete, insert)| (delete.end - delete.start, insert))
            .fold((0usize, 0usize), |(x1, y1), (x2, y2)| (x1 + x2, y1 + y2));

        // Update the range to account for modifications made to the original text.
        range.start = range.start - delete + insert;
        range.end = range.end - delete + insert;

        self.modified_text.replace_range(range, &argument_string);

        // Update the original file with the modified text.
        fs::write(&self.path, &self.modified_text).unwrap()
    }
}

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

// TODO: Enable filtering. Needs a better name.
fn update_counts() -> bool {
    env::var("UPDATE_EXPECT").is_ok()
}

fn to_abs_ws_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        return path.to_owned();
    }

    static WORKSPACE_ROOT: OnceCell<PathBuf> = OnceCell::new();
    WORKSPACE_ROOT
        .get_or_try_init(|| {
            let my_manifest = env::var("CARGO_MANIFEST_DIR")?;

            // Heuristic, see https://github.com/rust-lang/cargo/issues/3946
            let workspace_root = Path::new(&my_manifest)
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

#[cfg(test)]
mod test {
    use super::*;
    use snarkvm_utilities::{test_rng, UniformRand};

    use std::env;

    const ITERATIONS: u64 = 1024;

    #[test]
    fn check_position() {
        let count = count_is!(0, 0, 0, 0);
        assert_eq!(count.file, "circuits/environment/src/helpers/updatable_count.rs");
        assert_eq!(count.line, 279);
        assert_eq!(count.column, 21);
    }

    #[test]
    fn check_count_passes() {
        let original_count = count_is!(1, 2, 3, 4);
        let num_constants = 1;
        let num_public = 2;
        let num_private = 3;
        let num_inputs = 4;
        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);
    }

    #[test]
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
    fn check_count_updates_correctly() {
        // `original_count` is originally `count_is!(1, 2, 3, 4)`. Replace `original_count` to demonstrate replacement.
        let original_count = count_is!(5, 6, 7, 8);
        let num_constants = 5;
        let num_public = 6;
        let num_private = 7;
        let num_inputs = 8;

        // Set the environment variable to update the file.
        env::set_var("UPDATE_EXPECT", "1");

        original_count.assert_matches(num_constants, num_public, num_private, num_inputs);

        env::remove_var("UPDATE_EXPECT");
    }
}
