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

use super::*;

impl<
    G: AffineCurve<Coordinates = (BaseField<G>, BaseField<G>)>,
    P: MontgomeryParameters<BaseField = BaseField<G>> + TwistedEdwardsParameters<BaseField = BaseField<G>>,
> Elligator2<G, P>
{
    pub(super) const D: BaseField<G> = <P as TwistedEdwardsParameters>::COEFF_D;
    pub(super) const MONTGOMERY_A: BaseField<G> = <P as MontgomeryParameters>::COEFF_A;
    pub(super) const MONTGOMERY_B: BaseField<G> = <P as MontgomeryParameters>::COEFF_B;

    /// Returns the encoded affine group element and sign, given a field element.
    pub fn encode(input: &BaseField<G>) -> Result<(G, bool)> {
        ensure!(Self::D.legendre().is_qnr(), "D on the twisted Edwards curve must be a quadratic nonresidue");
        ensure!(!input.is_zero(), "Inputs to Elligator2 must be nonzero (inverses will fail)");

        let one = BaseField::<G>::one();

        // Store the sign of the input, to be returned with the output.
        let sign_high = input > &input.neg();

        // Compute the mapping from Fq to E(Fq) as a Montgomery element (u, v).
        let (u, v) = {
            // Compute the coefficients for the Weierstrass form: y^2 == x^3 + A * x^2 + B * x.
            let (a, b) = match Self::MONTGOMERY_B.inverse() {
                Some(b_inverse) => (Self::MONTGOMERY_A * b_inverse, b_inverse.square()),
                None => bail!("Montgomery B must be invertible in order to use Elligator2"),
            };

            // Let ur2 = D * input^2;
            let ur2 = Self::D * input.square();
            // Verify A^2 * ur^2 != B(1 + ur^2)^2.
            ensure!(a.square() * ur2 != b * (one + ur2).square(), "Elligator2 failed: A^2 * ur^2 == B(1 + ur^2)^2");

            // Let v = -A / (1 + ur^2).
            let v = -a * (one + ur2).inverse().ok_or_else(|| anyhow!("Elligator2 failed: (1 + ur^2) == 0"))?;

            // Let e = legendre(v^3 + Av^2 + Bv).
            let v2 = v.square();
            let e = ((v2 * v) + (a * v2) + (b * v)).legendre();

            // Let x = ev - ((1 - e) * A/2).
            let x = match e {
                LegendreSymbol::Zero => -a * BaseField::<G>::half(),
                LegendreSymbol::QuadraticResidue => v,
                LegendreSymbol::QuadraticNonResidue => -v - a,
            };

            // Let y = -e * sqrt(x^3 + Ax^2 + Bx).
            let x2 = x.square();
            let rhs = (x2 * x) + (a * x2) + (b * x);
            let value = rhs.sqrt().ok_or_else(|| anyhow!("Elligator2 failed: sqrt(x^3 + Ax^2 + Bx) failed"))?;
            let y = match e {
                LegendreSymbol::Zero => BaseField::<G>::zero(),
                LegendreSymbol::QuadraticResidue => -value,
                LegendreSymbol::QuadraticNonResidue => value,
            };

            // Ensure (x, y) is a valid Weierstrass element on: y^2 == x^3 + A * x^2 + B * x.
            ensure!(y.square() == rhs, "Elligator2 failed: y^2 != x^3 + A * x^2 + B * x");

            // Convert the Weierstrass element (x, y) to Montgomery element (u, v).
            let u = x * Self::MONTGOMERY_B;
            let v = y * Self::MONTGOMERY_B;

            // Ensure (u, v) is a valid Montgomery element on: B * v^2 == u^3 + A * u^2 + u
            let u2 = u.square();
            ensure!(
                Self::MONTGOMERY_B * v.square() == (u2 * u) + (Self::MONTGOMERY_A * u2) + u,
                "Elligator2 failed: B * v^2 != u^3 + A * u^2 + u"
            );

            (u, v)
        };

        // Convert the Montgomery element (u, v) to the twisted Edwards element (x, y).
        let x = u * v.inverse().ok_or_else(|| anyhow!("Elligator2 failed: v == 0"))?;
        let y = (u - one) * (u + one).inverse().ok_or_else(|| anyhow!("Elligator2 failed: (u + 1) == 0"))?;

        // Cofactor clear the twisted Edwards element (x, y).
        let group = G::from_coordinates((x, y)).mul_by_cofactor();
        ensure!(group.is_on_curve(), "Elligator2 failed: element is not on curve");
        ensure!(group.is_in_correct_subgroup_assuming_on_curve(), "Elligator2 failed: element in incorrect subgroup");

        Ok((group, sign_high))
    }
}
