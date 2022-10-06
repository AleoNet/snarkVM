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

//! This module contains functions to adjust randomly generated characters.
//! Some of the snarkVM internal tests involve the random generation of strings,
//! which are parsed and tested against the original ones.
//! However, since the string parser rejects certain characters,
//! if those characters are randomly generated, the tests fail.
//! To prevent these failures, as we randomly generate the characters,
//! we ensure that they are not among the ones rejected by the parser;
//! if they are, we adjust them to be allowed characters.
//! Note that the randomness of the characters is just for testing purposes
//! (there is no cryptographic requirement on this randomness),
//! and thus any statistical bias introduced by the adjustment is insignificant;
//! also note that the disallowed characters are a small fraction of the total set of characters,
//! and thus the adjustments rarely occur.

/// Adjust an unsafe character.
/// Since our parser rejects certain potentially unsafe characters
/// (see `Sanitizer::parse_safe_char`),
/// we need to avoid generating them randomly.
/// This function acts as an adjusting filter:
/// it changes an unsafe character to `'0'` (other choices are possible),
/// and leaves the other characters unchanged.
pub fn adjust_unsafe_char(ch: char) -> char {
    let code = ch as u32;
    if code < 9
        || code == 11
        || code == 12
        || (14..=31).contains(&code)
        || code == 127
        || (0x202a..=0x202e).contains(&code)
        || (0x2066..=0x2069).contains(&code)
    {
        '0'
    } else {
        ch
    }
}

/// Adjust a backslash and a double quote.
/// Aside from the characters rejected through the function [adjust_unsafe_char],
/// the syntax of strings allows backslash and double quotes only in certain circumstances:
/// backslash is used to introduce an escape,
/// and there are constraints on what can occur after a backslash;
/// double quotes is only used in escaped form just after a backslash.
/// If we randomly generate characters, we may end up generating
/// backslashes with malformed escape syntax,
/// or double quotes not preceded by backslash.
/// Thus, we also adjust backslashes and double quotes as we randomly generate characters.
/// Note that, this way, we do not test the parsing of any escape sequences;
/// to do that, we would need to reify the possible elements of strings,
/// namely characters and escapes,
/// and randomly generate such elements.
pub fn adjust_backslash_and_doublequote(ch: char) -> char {
    if ch == '\\' || ch == '\"' { '0' } else { ch }
}
