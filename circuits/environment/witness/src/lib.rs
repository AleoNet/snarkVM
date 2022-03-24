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

use proc_macro::TokenStream;
use quote::quote;
use syn::*;

#[proc_macro_attribute]
pub fn witness(_attrs: TokenStream, item: TokenStream) -> TokenStream {
    if let Ok(mut fun) = parse::<ItemFn>(item.clone()) {
        fun.block.stmts = parse_stmts(&mut fun.block.stmts);
        return quote!(#fun).into();
    }

    if let Ok(mut fun) = parse::<TraitItemMethod>(item.clone()) {
        if let Some(block) = fun.default.as_mut() {
            block.stmts = parse_stmts(&mut block.stmts);
            return quote!(#fun).into();
        }
    }

    if let Ok(mut fun) = parse::<ImplItemMethod>(item) {
        fun.block.stmts = parse_stmts(&mut fun.block.stmts);
        return quote!(#fun).into();
    }

    panic!("`witness` only works on functions")
}

#[cfg(feature = "witness")]
fn parse_stmts(stmts: &mut Vec<Stmt>) -> Vec<Stmt> {
    fn sanitize_stmt(stmt: &mut Stmt) -> String {
        let short = format!("{}", quote::ToTokens::into_token_stream(stmt)).chars().collect::<Vec<_>>();

        let short = short.into_iter().collect::<String>();
        short

        // let mut stream = quote::ToTokens::into_token_stream(stmt);
        //
        // let mut new_stream = Token
        //
        // for token in stream.into_iter() {
        //     match token {
        //         proc_macro::TokenTree::Ident(ident) => if ident.to_string() == "self".to_string() {
        //
        //         },
        //         other =>
        //     }
        // }
        //
        // stream.to_string()
    }

    let mut new_stmts = Vec::with_capacity(stmts.len());

    for stmt in stmts {
        let sanitized_stmt = sanitize_stmt(stmt);
        new_stmts.push(parse_quote!(#sanitized_stmt));
    }

    new_stmts
}

#[cfg(not(feature = "witness"))]
fn parse_stmts(stmts: &mut Vec<Stmt>) -> Vec<Stmt> {
    stmts.clone()
}
