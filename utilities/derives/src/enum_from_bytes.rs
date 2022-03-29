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

use proc_macro2::{Literal, TokenStream};
use quote::quote;
use syn::{parse::Parse, Data, Fields, Type};

pub(crate) fn impl_from_bytes(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    // Parse attributes and check that tag is a primitive integer type.
    // TODO: Allow only one tag attribute.
    let attribute = ast
        .attrs
        .iter()
        .find(|attr| attr.path.is_ident("tag"))
        .expect("`tag` attribute is required for deriving `EnumFromBytes`");
    let tag_type = attribute.parse_args_with(Type::parse).expect("`tag` attribute must be a type");
    match tag_type {
        Type::Path(ref tp) => match tp.path.segments.last() {
            Some(segment) => match segment.ident.to_string().as_str() {
                "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => {}
                _ => panic!("`tag` attribute must be a primitive integer type"),
            },
            None => panic!("Type path must have at least one segment."),
        },
        _ => panic!("`tag` attribute must be a primitive integer type for deriving `EnumFromBytes`"),
    }

    match ast.data {
        Data::Enum(ref data_enum) => {
            let mut match_cases = Vec::<TokenStream>::with_capacity(data_enum.variants.len());

            for (i, variant) in data_enum.variants.iter().enumerate() {
                let variant_name = &variant.ident;
                let variant_index = Literal::usize_unsuffixed(i);
                let match_arm = match &variant.fields {
                    Fields::Named(fields) => {
                        let mut field_reads = Vec::<TokenStream>::with_capacity(fields.named.len());

                        for field in fields.named.iter() {
                            let ty = &field.ty;
                            field_reads.push(quote! {
                                #ty::read_le(&mut reader)?
                            });
                        }

                        quote! {
                            Ok(#variant_index) => Ok(Self::#variant_name(#(#field_reads),*))
                        }
                    }
                    Fields::Unnamed(fields) => {
                        let mut field_reads = Vec::<TokenStream>::with_capacity(fields.unnamed.len());

                        for field in fields.unnamed.iter() {
                            let ty = match &field.ty {
                                Type::Path(tp) => tp
                                    .path
                                    .segments
                                    .last()
                                    .expect("Expected path to contain at least one segment")
                                    .ident
                                    .clone(),
                                _ => panic!("Expected field type to be a path."),
                            };
                            field_reads.push(quote! {
                                #ty::read_le(&mut reader)?
                            });
                        }

                        quote! {
                            Ok(#variant_index) => Ok(Self::#variant_name(#(#field_reads),*))
                        }
                    }
                    Fields::Unit => {
                        quote! {
                            Ok(#variant_index) => Ok(Self::#variant_name)
                        }
                    }
                };
                match_cases.push(match_arm);
            }

            let gen = quote! {
                impl #impl_generics snarkvm_utilities::bytes::FromBytes for #name #ty_generics #where_clause {
                    fn read_le<R: std::io::Read>(mut reader: R) -> std::io::Result<Self> {
                        match #tag_type::read_le(&mut reader) {
                            #(#match_cases),*,
                            Ok(code) => Err(snarkvm_utilities::error(format!("Unrecognized variant number {} for {}", code, stringify!(#name)))),
                            Err(err) => Err(err),
                        }
                    }
                }
            };
            gen
        }
        _ => panic!("EnumFromBytes can only be derived for enums, {} is not an enum", name),
    }
}
