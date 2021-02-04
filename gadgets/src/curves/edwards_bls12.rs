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

use crate::curves::templates::twisted_edwards::AffineGadget;
use snarkvm_curves::edwards_bls12::{EdwardsParameters, Fq};
use snarkvm_models::gadgets::curves::FpGadget;

pub type FqGadget = FpGadget<Fq>;
pub type EdwardsBlsGadget = AffineGadget<EdwardsParameters, Fq, FqGadget>;

#[cfg(test)]
mod test {
    use super::EdwardsBlsGadget;
    use crate::curves::templates::twisted_edwards::test::{edwards_constraint_costs, edwards_test};
    use snarkvm_curves::edwards_bls12::{EdwardsParameters, Fq};
    use snarkvm_models::gadgets::r1cs::TestConstraintSystem;

    #[test]
    fn edwards_constraint_costs_test() {
        let mut cs = TestConstraintSystem::<Fq>::new();
        edwards_constraint_costs::<_, EdwardsParameters, EdwardsBlsGadget, _>(&mut cs);
        assert!(cs.is_satisfied());
    }

    #[test]
    fn edwards_bls12_gadget_test() {
        let mut cs = TestConstraintSystem::<Fq>::new();
        edwards_test::<_, EdwardsParameters, EdwardsBlsGadget, _>(&mut cs);
        assert!(cs.is_satisfied());
    }
}
