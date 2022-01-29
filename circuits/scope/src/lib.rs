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

extern crate proc_macro;

#[macro_use]
extern crate quote;

#[macro_use]
extern crate syn;

enum Type {
    Custom,
    Method,
    Circuit,
    Standard,
}

fn extract_literal(token_tree: &proc_macro::TokenTree) -> String {
    match token_tree {
        // String literals seem to come through including their double quotes. Trim them off.
        proc_macro::TokenTree::Literal(literal) => literal.to_string().trim().trim_matches('"').trim().to_string(),
        proc_macro::TokenTree::Ident(ident) => ident.to_string().trim().trim_matches('"').trim().to_string(),
        _ => panic!("Invalid argument. Specify at most one argument - `custom = XX`, `method = XX`, or `circuit = XX`"),
    }
}

/// Returns the function name with parenthesis, as the scope name.
fn get_scope_name(metadata: proc_macro::TokenStream, function_name: &str) -> (Type, String) {
    // Grab everything into a vector and filter out any intervening punctuation
    // (commas come through as TokenTree::Punct(_)).
    let macro_arguments: Vec<proc_macro::TokenTree> = metadata
        .into_iter()
        .filter(|token| match token {
            proc_macro::TokenTree::Ident(_) => true,
            proc_macro::TokenTree::Literal(_) => true,
            _ => false,
        })
        .collect();

    if macro_arguments.is_empty() {
        (Type::Standard, format!("{}()", function_name))
    } else if macro_arguments.len() == 2 {
        // Example: For "scope(method = "add")", this will parse as ["method", "add"].
        let argument_type = extract_literal(&macro_arguments[0]);
        let name = extract_literal(&macro_arguments[1]);

        if name.contains('.') {
            panic!("Scope names cannot contain periods (\".\")")
        }

        match argument_type.trim() {
            "custom" => (Type::Custom, name.to_string()),
            "method" => (Type::Method, format!("{}()", name)),
            "circuit" => (Type::Circuit, format!("{}::{}()", name, function_name)),
            _ => panic!("Invalid argument. Specify `custom = XX`, `method = XX`, or `circuit = XX`"),
        }
    } else {
        panic!("Specify at most one argument, to customize the scope name");
    }
}

/// Examples:
///     #[scope]
///     #[scope(method = "add")]         -> add()
///     #[scope(circuit = "BaseField")]  -> BaseField::add()
///     #[scope(custom = "hello world")] -> hello world
#[cfg(feature = "scope")]
#[proc_macro_attribute]
pub fn scope(metadata: proc_macro::TokenStream, input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input_fn: syn::ItemFn = parse_macro_input!(input as syn::ItemFn);
    let visibility = input_fn.vis;
    let ident = input_fn.ident;
    let inputs = input_fn.decl.inputs;
    let output = input_fn.decl.output;
    let generics = &input_fn.decl.generics;
    let where_clause = &input_fn.decl.generics.where_clause;
    let block = input_fn.block;

    let (argument_type, scope_name) = get_scope_name(metadata, &ident.to_string());

    (quote!(
        #visibility fn #ident #generics (#inputs) #output #where_clause {
            // let _tmr = ::aleo_std::prelude::timer!(#scope_name);
            // ::snarkvm_circuits_environment::scoped!(#scope_name, #block)
            #block
        }
    ))
    .into()

    // match argument_type {
    //     Type::Circuit => {
    //         (quote!(
    //             #visibility fn #ident #generics (#inputs) #output #where_clause {
    //                 // let _tmr = ::aleo_std::prelude::timer!(#scope_name);
    //                 // ::snarkvm_circuits_environment::push_scope!(#scope_name);
    //                 // ::snarkvm_circuits_environment::scoped!(#scope_name, #block)
    //                 #block
    //             }
    //         ))
    //         .into()
    //     }
    //     _ => {
    //         (quote!(
    //             #visibility fn #ident #generics (#inputs) #output #where_clause {
    //                 // let _tmr = ::aleo_std::prelude::timer!(#scope_name);
    //                 // ::snarkvm_circuits_environment::scoped!(#scope_name, #block)
    //                 #block
    //             }
    //         ))
    //         .into()
    //     }
    // }
}

#[cfg(not(feature = "scope"))]
#[proc_macro_attribute]
pub fn scope(_metadata: proc_macro::TokenStream, input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    proc_macro::TokenStream::from(input).into()
}
