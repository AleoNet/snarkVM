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

use proc_macro2::{Ident, Span};
use proc_macro_crate::crate_name;
use quote::quote;
use syn::ItemFn;

pub(crate) fn generate_test_function(function: ItemFn) -> proc_macro::TokenStream {
    let name = &function.sig.ident;
    let crate_name =
        Ident::new(&crate_name("snarkos-metrics").unwrap_or_else(|_| "crate".to_string()), Span::call_site());
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
