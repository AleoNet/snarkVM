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

// TODO: Refactor macros one all operations implement `MetadataForOp`.

#[macro_export]
macro_rules! assert_count {
    ($type_:ty, $oper:path, $case:expr) => {
        $crate::print_scope!();

        let Count(num_constants, num_public, num_private, num_constraints) =
            <$type_ as CountForOp<dyn $oper>>::count($case);
        assert!(num_constants.is_satisfied(Circuit::num_constants_in_scope()), "(num_constants)");
        assert!(num_public.is_satisfied(Circuit::num_public_in_scope()), "(num_public)");
        assert!(num_private.is_satisfied(Circuit::num_private_in_scope()), "(num_private)");
        assert!(num_constraints.is_satisfied(Circuit::num_constraints_in_scope()), "(num_constraints)");
        assert!(Circuit::is_satisfied_in_scope(), "(is_satisfied_in_scope)");
    };
}

#[macro_export]
macro_rules! assert_count_fails {
    ($type_:ty, $oper:path, $case:expr) => {
        $crate::print_scope!();

        let Count(num_constants, num_public, num_private, num_constraints) =
            <$type_ as CountForOp<dyn $oper>>::count($case);
        assert!(num_constants.is_satisfied(Circuit::num_constants_in_scope()), "(num_constants)");
        assert!(num_public.is_satisfied(Circuit::num_public_in_scope()), "(num_public)");
        assert!(num_private.is_satisfied(Circuit::num_private_in_scope()), "(num_private)");
        assert!(num_constraints.is_satisfied(Circuit::num_constraints_in_scope()), "(num_constraints)");
        assert!(!Circuit::is_satisfied_in_scope(), "(!is_satisfied_in_scope)");
    };
}

#[macro_export]
macro_rules! assert_output_mode {
    ($candidate: expr, $type_:ty, $oper:path, $case:expr) => {
        let expected_mode = <$type_ as OutputModeForOp<dyn $oper>>::output_mode($case);
        assert_eq!(expected_mode, $candidate.eject_mode());
    };
}
