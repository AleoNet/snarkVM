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

use proc_macro2::{Ident, Span, TokenStream};
use proc_macro_crate::crate_name;
use proc_macro_error::{abort_call_site, proc_macro_error};
use syn::*;

use quote::{quote, ToTokens};

#[proc_macro_derive(CanonicalSerialize)]
pub fn derive_canonical_serialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(impl_canonical_serialize(&ast))
}

enum IdentOrIndex {
    Ident(proc_macro2::Ident),
    Index(Index),
}

impl ToTokens for IdentOrIndex {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::Ident(ident) => ident.to_tokens(tokens),
            Self::Index(index) => index.to_tokens(tokens),
        }
    }
}

fn impl_serialize_field(
    serialize_body: &mut Vec<TokenStream>,
    serialized_size_body: &mut Vec<TokenStream>,
    serialize_uncompressed_body: &mut Vec<TokenStream>,
    uncompressed_size_body: &mut Vec<TokenStream>,
    idents: &mut Vec<IdentOrIndex>,
    ty: &Type,
) {
    // Check if type is a tuple.
    match ty {
        Type::Tuple(tuple) => {
            for (i, elem_ty) in tuple.elems.iter().enumerate() {
                let index = Index::from(i);
                idents.push(IdentOrIndex::Index(index));
                impl_serialize_field(
                    serialize_body,
                    serialized_size_body,
                    serialize_uncompressed_body,
                    uncompressed_size_body,
                    idents,
                    elem_ty,
                );
                idents.pop();
            }
        }
        _ => {
            serialize_body.push(quote! { CanonicalSerialize::serialize(&self.#(#idents).*, writer)?; });
            serialized_size_body.push(quote! { size += CanonicalSerialize::serialized_size(&self.#(#idents).*); });
            serialize_uncompressed_body
                .push(quote! { CanonicalSerialize::serialize_uncompressed(&self.#(#idents).*, writer)?; });
            uncompressed_size_body.push(quote! { size += CanonicalSerialize::uncompressed_size(&self.#(#idents).*); });
        }
    }
}

fn impl_canonical_serialize(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let len = if let Data::Struct(ref data_struct) = ast.data {
        data_struct.fields.len()
    } else {
        panic!("Serialize can only be derived for structs, {} is not a struct", name);
    };

    let mut serialize_body = Vec::<TokenStream>::with_capacity(len);
    let mut serialized_size_body = Vec::<TokenStream>::with_capacity(len);
    let mut serialize_uncompressed_body = Vec::<TokenStream>::with_capacity(len);
    let mut uncompressed_size_body = Vec::<TokenStream>::with_capacity(len);

    match ast.data {
        Data::Struct(ref data_struct) => {
            let mut idents = Vec::<IdentOrIndex>::new();

            for (i, field) in data_struct.fields.iter().enumerate() {
                match field.ident {
                    None => {
                        let index = Index::from(i);
                        idents.push(IdentOrIndex::Index(index));
                    }
                    Some(ref ident) => {
                        idents.push(IdentOrIndex::Ident(ident.clone()));
                    }
                }

                impl_serialize_field(
                    &mut serialize_body,
                    &mut serialized_size_body,
                    &mut serialize_uncompressed_body,
                    &mut uncompressed_size_body,
                    &mut idents,
                    &field.ty,
                );

                idents.clear();
            }
        }
        _ => panic!("Serialize can only be derived for structs, {} is not a struct", name),
    };

    let gen = quote! {
        impl #impl_generics CanonicalSerialize for #name #ty_generics #where_clause {
            #[allow(unused_mut, unused_variables)]
            fn serialize<W: snarkvm_utilities::Write>(&self, writer: &mut W) -> Result<(), snarkvm_utilities::SerializationError> {
                #(#serialize_body)*
                Ok(())
            }
            #[allow(unused_mut, unused_variables)]
            fn serialized_size(&self) -> usize {
                let mut size = 0;
                #(#serialized_size_body)*
                size
            }
            #[allow(unused_mut, unused_variables)]
            fn serialize_uncompressed<W: snarkvm_utilities::Write>(&self, writer: &mut W) -> Result<(), snarkvm_utilities::SerializationError> {
                #(#serialize_uncompressed_body)*
                Ok(())
            }
            #[allow(unused_mut, unused_variables)]
            fn uncompressed_size(&self) -> usize {
                let mut size = 0;
                #(#uncompressed_size_body)*
                size
            }
        }
    };
    gen
}

#[proc_macro_derive(CanonicalDeserialize)]
pub fn derive_canonical_deserialize(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    proc_macro::TokenStream::from(impl_canonical_deserialize(&ast))
}

/// Returns two TokenStreams, one for the compressed deserialize, one for the
/// uncompressed.
fn impl_deserialize_field(ty: &Type) -> (TokenStream, TokenStream) {
    // Check if type is a tuple.
    match ty {
        Type::Tuple(tuple) => {
            let (compressed_fields, uncompressed_fields): (Vec<_>, Vec<_>) =
                tuple.elems.iter().map(impl_deserialize_field).unzip();
            (quote! { (#(#compressed_fields)*), }, quote! { (#(#uncompressed_fields)*), })
        }
        _ => (
            quote! { CanonicalDeserialize::deserialize(reader)?, },
            quote! { CanonicalDeserialize::deserialize_uncompressed(reader)?, },
        ),
    }
}

fn impl_canonical_deserialize(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let deserialize_body;
    let deserialize_uncompressed_body;

    match ast.data {
        Data::Struct(ref data_struct) => {
            let mut tuple = false;
            let mut compressed_field_cases = Vec::<TokenStream>::with_capacity(data_struct.fields.len());
            let mut uncompressed_field_cases = Vec::<TokenStream>::with_capacity(data_struct.fields.len());
            for field in data_struct.fields.iter() {
                match &field.ident {
                    None => {
                        tuple = true;
                        let (compressed, uncompressed) = impl_deserialize_field(&field.ty);
                        compressed_field_cases.push(compressed);
                        uncompressed_field_cases.push(uncompressed);
                    }
                    // struct field without len_type
                    Some(ident) => {
                        let (compressed_field, uncompressed_field) = impl_deserialize_field(&field.ty);
                        compressed_field_cases.push(quote! { #ident: #compressed_field });
                        uncompressed_field_cases.push(quote! { #ident: #uncompressed_field });
                    }
                }
            }

            if tuple {
                deserialize_body = quote!({
                    Ok(#name (
                        #(#compressed_field_cases)*
                    ))
                });
                deserialize_uncompressed_body = quote!({
                    Ok(#name (
                        #(#uncompressed_field_cases)*
                    ))
                });
            } else {
                deserialize_body = quote!({
                    Ok(#name {
                        #(#compressed_field_cases)*
                    })
                });
                deserialize_uncompressed_body = quote!({
                    Ok(#name {
                        #(#uncompressed_field_cases)*
                    })
                });
            }
        }
        _ => panic!("Deserialize can only be derived for structs, {} is not a Struct", name),
    };

    let gen = quote! {
        impl #impl_generics CanonicalDeserialize for #name #ty_generics #where_clause {
            #[allow(unused_mut,unused_variables)]
            fn deserialize<R: snarkvm_utilities::Read>(reader: &mut R) -> Result<Self, snarkvm_utilities::SerializationError> {
                #deserialize_body
            }
            #[allow(unused_mut,unused_variables)]
            fn deserialize_uncompressed<R: snarkvm_utilities::Read>(reader: &mut R) -> Result<Self, snarkvm_utilities::SerializationError> {
                #deserialize_uncompressed_body
            }
        }
    };
    gen
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn test_with_metrics(_: proc_macro::TokenStream, item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match parse::<ItemFn>(item.clone()) {
        Ok(function) => {
            fn generate_test_function(function: ItemFn, crate_name: Ident) -> proc_macro::TokenStream {
                let name = &function.sig.ident;
                let statements = function.block.stmts;
                (quote! {
                    // Generates a new test with Prometheus registry checks, and enforces
                    // that the test runs serially with other tests that use metrics.
                    #[test]
                    #[serial]
                    fn #name() {
                        // Initialize Prometheus once in the test environment.
                        #crate_name::testing::initialize_prometheus_for_testing();
                        // Check that all metrics are 0 or empty.
                        assert_eq!(0, #crate_name::Metrics::get_connected_peers());
                        // Run the test logic.
                        #(#statements)*
                        // Check that all metrics are reset to 0 or empty (for next test).
                        assert_eq!(0, Metrics::get_connected_peers());
                    }
                })
                .into()
            }
            let name = crate_name("snarkos-metrics").unwrap_or_else(|_| "crate".to_string());
            let crate_name = Ident::new(&name, Span::call_site());
            generate_test_function(function, crate_name)
        }
        _ => abort_call_site!("test_with_metrics only works on functions"),
    }
}
