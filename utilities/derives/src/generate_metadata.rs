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

use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::*;

pub(crate) fn generate_impl(attr_args: AttributeArgs, item: Item) -> TokenStream {
    // Validate the attribute arguments.

    // There must be 1 or 2 arguments.
    match attr_args.len() == 1 || attr_args.len() == 2 {
        true => (),
        false => panic!("The attribute macro `generate_metadata_impl` must have 1 or 2 arguments."),
    }

    // Validate the first argument.
    // It must be of the form `generate = <bool>`.
    // This use of unwrap is safe since we check that there is either 1 or 2 elements in `attr_args`.
    let generate = match attr_args.get(0).unwrap() {
        NestedMeta::Meta(Meta::NameValue(MetaNameValue { path, lit: Lit::Bool(literal), .. })) => {
            match path.get_ident() {
                Some(ident) if ident.to_string().eq("generate") => literal.value,
                _ => panic!(
                    "The first argument to the attribute macro `generate_metadata_impl` must be of the form `generate = <bool>`."
                ),
            }
        }
        _ => panic!(
            "The first argument to the attribute macro `generate_metadata_impl` must be of the form `generate = <bool>`."
        ),
    };

    // Validate the second argument if it is provided.
    // The second argument must be of the form `runs = <usize>`.
    let _runs = match attr_args.get(1) {
        None => 0usize, // Do nothing
        Some(NestedMeta::Meta(Meta::NameValue(MetaNameValue { path, lit: Lit::Int(literal), .. }))) => {
            match path.get_ident() {
                Some(ident) if ident.to_string().eq("runs") => match literal.base10_parse::<usize>() {
                    Ok(value) => value,
                    Err(_) => panic!("Unable to parse the value associated with `runs` as a usize."),
                },
                _ => panic!(
                    "The second argument to the attribute macro `generate_metadata_impl` must be of the form `runs = <usize>`."
                ),
            }
        }
        _ => panic!(
            "The second argument to the attribute macro `generate_metadata_impl` must be of the form `name = <usize>`."
        ),
    };

    if generate {
        println!("TODO: Generate metadata.");
    }

    item.into_token_stream()
}
