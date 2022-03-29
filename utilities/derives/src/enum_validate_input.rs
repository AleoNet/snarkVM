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

use syn::{parse::Parse, Data, DataEnum, Type};

// Validates the AST provided to the derive macro.
pub(crate) fn validate_input_ast(ast: &syn::DeriveInput) -> (&DataEnum, Type) {
    // Parse attributes and checks that tag is a primitive integer type.
    // Note that only the first `tag` is used.
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
        Data::Enum(ref data_enum) => (data_enum, tag_type),
        _ => panic!("EnumToBytes can only be derived for enums, {} is not an enum", ast.ident),
    }
}
