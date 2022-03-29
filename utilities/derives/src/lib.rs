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

mod canonical_deserialize;

mod canonical_serialize;

mod enum_from_bytes;

mod enum_to_bytes;

mod test_with_metrics;

use proc_macro_error::{abort_call_site, proc_macro_error};
use syn::*;

#[proc_macro_derive(CanonicalSerialize)]
pub fn derive_canonical_serialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(canonical_serialize::impl_canonical_serialize(&ast))
}

#[proc_macro_derive(CanonicalDeserialize)]
pub fn derive_canonical_deserialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(canonical_deserialize::impl_canonical_deserialize(&ast))
}

#[proc_macro_derive(EnumFromBytes, attributes(tag))]
pub fn derive_enum_from_bytes(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(enum_from_bytes::impl_from_bytes(&ast))
}

#[proc_macro_derive(EnumToBytes, attributes(tag))]
pub fn derive_enum_to_bytes(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(enum_to_bytes::impl_to_bytes(&ast))
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn test_with_metrics(_: proc_macro::TokenStream, item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match parse::<ItemFn>(item.clone()) {
        Ok(function) => test_with_metrics::generate_test_function(function),
        _ => abort_call_site!("test_with_metrics only works on functions"),
    }
}
