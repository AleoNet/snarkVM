// Copyright (C) 2019-2021 Aleo Systems Inc.
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
    idents: &mut Vec<IdentOrIndex>,
    ty: &Type,
) {
    // Check if type is a tuple.
    match ty {
        Type::Tuple(tuple) => {
            for (i, elem_ty) in tuple.elems.iter().enumerate() {
                let index = Index::from(i);
                idents.push(IdentOrIndex::Index(index));
                impl_serialize_field(serialize_body, serialized_size_body, idents, elem_ty);
                idents.pop();
            }
        }
        _ => {
            serialize_body
                .push(quote! { CanonicalSerialize::serialize_with_mode(&self.#(#idents).*, &mut writer, compress)?; });
            serialized_size_body
                .push(quote! { size += CanonicalSerialize::serialized_size(&self.#(#idents).*, compress); });
        }
    }
}

fn impl_canonical_serialize(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let len = if let Data::Struct(ref data_struct) = ast.data {
        data_struct.fields.len()
    } else {
        panic!(
            "`CanonicalSerialize` can only be derived for structs, {} is not a struct",
            name
        );
    };

    let mut serialize_body = Vec::<TokenStream>::with_capacity(len);
    let mut serialized_size_body = Vec::<TokenStream>::with_capacity(len);

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

                impl_serialize_field(&mut serialize_body, &mut serialized_size_body, &mut idents, &field.ty);

                idents.clear();
            }
        }
        _ => panic!(
            "`CanonicalSerialize` can only be derived for structs, {} is not a struct",
            name
        ),
    };

    let gen = quote! {
        impl #impl_generics CanonicalSerialize for #name #ty_generics #where_clause {
            #[allow(unused_mut, unused_variables)]
            fn serialize_with_mode<W: Write>(&self, mut writer: W, compress: snarkvm_utilities::serialize::Compress) -> Result<(), SerializationError> {
                #(#serialize_body)*
                Ok(())
            }
            #[allow(unused_mut, unused_variables)]
            fn serialized_size(&self, compress: snarkvm_utilities::serialize::Compress) -> usize {
                let mut size = 0;
                #(#serialized_size_body)*
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

fn impl_valid_field(
    check_body: &mut Vec<TokenStream>,
    batch_check_body: &mut Vec<TokenStream>,
    idents: &mut Vec<IdentOrIndex>,
    ty: &Type,
) {
    // Check if type is a tuple.
    match ty {
        Type::Tuple(tuple) => {
            for (i, elem_ty) in tuple.elems.iter().enumerate() {
                let index = Index::from(i);
                idents.push(IdentOrIndex::Index(index));
                impl_valid_field(check_body, batch_check_body, idents, elem_ty);
                idents.pop();
            }
        }
        _ => {
            check_body.push(quote! { Valid::check(&self.#(#idents).*)?; });
            batch_check_body.push(quote! { Valid::batch_check(batch.iter().map(|v| &v.#(#idents).*))?; });
        }
    }
}

fn impl_valid(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let len = if let Data::Struct(ref data_struct) = ast.data {
        data_struct.fields.len()
    } else {
        panic!("`Valid` can only be derived for structs, {} is not a struct", name);
    };

    let mut check_body = Vec::<TokenStream>::with_capacity(len);
    let mut batch_body = Vec::<TokenStream>::with_capacity(len);

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

                impl_valid_field(&mut check_body, &mut batch_body, &mut idents, &field.ty);

                idents.clear();
            }
        }
        _ => panic!("`Valid` can only be derived for structs, {} is not a struct", name),
    };

    let gen = quote! {
        impl #impl_generics Valid for #name #ty_generics #where_clause {
            #[allow(unused_mut, unused_variables)]
            fn check(&self) -> Result<(), SerializationError> {
                #(#check_body)*
                Ok(())
            }
            #[allow(unused_mut, unused_variables)]
            fn batch_check<'a>(batch: impl Iterator<Item = &'a Self> + Send) -> Result<(), SerializationError>
                where
            Self: 'a
            {

                let batch: Vec<_> = batch.collect();
                #(#batch_body)*
                Ok(())
            }
        }
    };
    gen
}

/// Returns a `TokenStream` for `deserialize_with_mode`.
/// uncompressed.
fn impl_deserialize_field(ty: &Type) -> TokenStream {
    // Check if type is a tuple.
    match ty {
        Type::Tuple(tuple) => {
            let compressed_fields: Vec<_> = tuple
                .elems
                .iter()
                .map(|elem_ty| impl_deserialize_field(elem_ty))
                .collect();
            quote! { (#(#compressed_fields)*), }
        }
        _ => quote! { CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?, },
    }
}

fn impl_canonical_deserialize(ast: &syn::DeriveInput) -> TokenStream {
    let valid_impl = impl_valid(ast);
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let deserialize_body;

    match ast.data {
        Data::Struct(ref data_struct) => {
            let mut field_cases = Vec::<TokenStream>::with_capacity(data_struct.fields.len());
            let mut tuple = false;
            for field in data_struct.fields.iter() {
                match &field.ident {
                    None => {
                        tuple = true;
                        let compressed = impl_deserialize_field(&field.ty);
                        field_cases.push(compressed);
                    }
                    // struct field without len_type
                    Some(ident) => {
                        let compressed = impl_deserialize_field(&field.ty);
                        field_cases.push(quote! { #ident: #compressed });
                    }
                }
            }

            deserialize_body = if tuple {
                quote!({
                    Ok(#name (
                        #(#field_cases)*
                     ))
                })
            } else {
                quote!({
                    Ok(#name {
                        #(#field_cases)*
                    })
                })
            };
        }
        _ => panic!(
            "`CanonicalDeserialize` can only be derived for structs, {} is not a Struct",
            name
        ),
    };

    let mut gen = quote! {
        impl #impl_generics CanonicalDeserialize for #name #ty_generics #where_clause {
            #[allow(unused_mut,unused_variables)]
            fn deserialize_with_mode<R: Read>(
                mut reader: R,
                compress: snarkvm_utilities::serialize::Compress,
                validate: snarkvm_utilities::serialize::Validate,
            ) -> Result<Self, SerializationError> {
                #deserialize_body
            }
        }
    };
    gen.extend(valid_impl);
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
