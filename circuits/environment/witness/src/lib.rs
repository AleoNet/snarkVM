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

extern crate proc_macro;

use proc_macro::{Group, Ident, TokenStream, TokenTree};

fn recursively_replace_self(stream: TokenStream, replacement: &str) -> TokenStream {
    stream
        .into_iter()
        .map(|item| match item {
            TokenTree::Ident(ident) => {
                if ident.to_string() == "self" {
                    TokenTree::Ident(Ident::new(replacement, ident.span()))
                } else {
                    TokenTree::Ident(ident)
                }
            }
            TokenTree::Group(group) => {
                TokenTree::Group(Group::new(group.delimiter(), recursively_replace_self(group.stream(), replacement)))
            }
            i => i,
        })
        .collect()
}

#[proc_macro]
pub fn rename_selfs(stream: TokenStream) -> TokenStream {
    recursively_replace_self(stream, "_self")
}
