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
use quote::quote;
use syn::{Data, Type};

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

pub(crate) fn impl_canonical_deserialize(ast: &syn::DeriveInput) -> TokenStream {
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
