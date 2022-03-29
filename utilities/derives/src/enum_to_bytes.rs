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
use quote::quote;
use syn::{parse::Parse, Data, Fields, Type};

pub(crate) fn impl_to_bytes(ast: &syn::DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    // Parse attributes and check that tag is a primitive integer type.
    // TODO: Allow only one tag attribute.
    let attribute = ast
        .attrs
        .iter()
        .find(|attr| attr.path.is_ident("tag"))
        .expect("`tag` attribute is required for deriving `EnumToBytes`");
    let tag_type = attribute.parse_args_with(Type::parse).expect("`tag` attribute must be a type");
    match tag_type {
        Type::Path(ref tp) => match tp.path.segments.last() {
            Some(segment) => match segment.ident.to_string().as_str() {
                "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => {}
                _ => panic!("`tag` attribute must be a primitive integer type"),
            },
            None => panic!("Type path must have at least one segment."),
        },
        _ => panic!("`tag` attribute must be a primitive integer type for deriving `EnumToBytes`"),
    }

    match ast.data {
        Data::Enum(ref data_enum) => {
            let mut match_cases = Vec::<TokenStream>::with_capacity(data_enum.variants.len());

            for (variant_index, variant) in data_enum.variants.iter().enumerate() {
                let variant_name = &variant.ident;
                let match_arm = match &variant.fields {
                    Fields::Named(fields) => {
                        let mut field_patterns = Vec::<TokenStream>::with_capacity(fields.named.len());
                        let mut field_writes = Vec::<TokenStream>::with_capacity(fields.named.len());

                        for (i, field) in fields.named.iter().enumerate() {
                            let pattern = field.ident.as_ref().unwrap();
                            field_patterns.push(quote! {
                                #pattern
                            });
                            if i == fields.named.len() - 1 {
                                field_writes.push(quote! {
                                    #pattern.write_le(&mut writer)
                                });
                            } else {
                                field_writes.push(quote! {
                                    #pattern.write_le(&mut writer)?;
                                });
                            }
                        }

                        quote! {
                            #variant_name{#(#field_patterns),*} => {
                                (#variant_index as #tag_type).write_le(&mut writer)?;
                                #(#field_writes)*
                            }
                        }
                    }
                    Fields::Unnamed(fields) => {
                        let mut field_patterns = Vec::<TokenStream>::with_capacity(fields.unnamed.len());
                        let mut field_writes = Vec::<TokenStream>::with_capacity(fields.unnamed.len());

                        for (i, _) in fields.unnamed.iter().enumerate() {
                            let pattern = Ident::new(&format!("field_{}", i), Span::call_site());
                            field_patterns.push(quote! {
                                #pattern
                            });
                            if i == fields.unnamed.len() - 1 {
                                field_writes.push(quote! {
                                    #pattern.write_le(&mut writer)
                                });
                            } else {
                                field_writes.push(quote! {
                                    #pattern.write_le(&mut writer)?;
                                });
                            }
                        }

                        quote! {
                            #name::#variant_name(#(#field_patterns),*) => {
                                (#variant_index as #tag_type).write_le(&mut writer)?;
                                #(#field_writes)*
                            }
                        }
                    }
                    Fields::Unit => {
                        quote! {
                            #name::#variant_name => {
                                (#variant_index as #tag_type).write_le(&mut writer)
                            }
                        }
                    }
                };
                match_cases.push(match_arm);
            }

            let gen = quote! {
                impl #impl_generics snarkvm_utilities::bytes::ToBytes for #name #ty_generics #where_clause {
                    fn write_le<W: std::io::Write>(&self, mut writer: W) -> std::io::Result<()> {
                        match self {
                            #(#match_cases)*
                        }
                    }
                }
            };
            gen
        }
        _ => panic!("EnumToBytes can only be derived for enums, {} is not an enum", name),
    }
}
