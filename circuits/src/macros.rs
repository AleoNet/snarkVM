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

#[macro_export]
macro_rules! assert_circuit {
    () => {
        println!("Constants: {:?}", Circuit::num_constants_in_scope());
        println!("Public: {:?}", Circuit::num_public_in_scope());
        println!("Private: {:?}", Circuit::num_private_in_scope());
        println!("Constraints: {:?}", Circuit::num_constraints_in_scope());

        assert!(Circuit::is_satisfied(), "(is_satisfied)");
    };
    ($num_constants:expr, $num_public:expr, $num_private:expr, $num_constraints:expr) => {
        println!("Constants: {:?}", Circuit::num_constants_in_scope());
        println!("Public: {:?}", Circuit::num_public_in_scope());
        println!("Private: {:?}", Circuit::num_private_in_scope());
        println!("Constraints: {:?}", Circuit::num_constraints_in_scope());

        assert_eq!($num_constants, Circuit::num_constants_in_scope(), "(num_constants)");
        assert_eq!($num_public, Circuit::num_public_in_scope(), "(num_public)");
        assert_eq!($num_private, Circuit::num_private_in_scope(), "(num_private)");
        assert_eq!($num_constraints, Circuit::num_constraints_in_scope(), "(num_constraints)");
        assert!(Circuit::is_satisfied(), "(is_satisfied)");
    };
    ($case:expr, $num_constants:expr, $num_public:expr, $num_private:expr, $num_constraints:expr) => {
        println!("Constants: {:?}", Circuit::num_constants_in_scope());
        println!("Public: {:?}", Circuit::num_public_in_scope());
        println!("Private: {:?}", Circuit::num_private_in_scope());
        println!("Constraints: {:?}", Circuit::num_constraints_in_scope());

        assert_eq!($num_constants, Circuit::num_constants_in_scope(), "{} (num_constants)", $case);
        assert_eq!($num_public, Circuit::num_public_in_scope(), "{} (num_public)", $case);
        assert_eq!($num_private, Circuit::num_private_in_scope(), "{} (num_private)", $case);
        assert_eq!($num_constraints, Circuit::num_constraints_in_scope(), "{} (num_constraints)", $case);
        assert!(Circuit::is_satisfied(), "{} (is_satisfied)", $case);
    };
}
