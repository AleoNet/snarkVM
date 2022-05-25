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

use snarkvm_curves::{AffineCurve, MontgomeryParameters, TwistedEdwardsParameters};
use snarkvm_fields::{Field, LegendreSymbol, One, SquareRootField, Zero};

use anyhow::{bail, ensure, Result};
use core::{cmp, marker::PhantomData, ops::Neg};

type BaseField<G> = <G as AffineCurve>::BaseField;

pub struct Elligator2<
    G: AffineCurve<Coordinates = (BaseField<G>, BaseField<G>)>,
    P: MontgomeryParameters<BaseField = BaseField<G>> + TwistedEdwardsParameters<BaseField = BaseField<G>>,
>(PhantomData<(G, P)>);

impl<
    G: AffineCurve<Coordinates = (BaseField<G>, BaseField<G>)>,
    P: MontgomeryParameters<BaseField = BaseField<G>> + TwistedEdwardsParameters<BaseField = BaseField<G>>,
> Elligator2<G, P>
{
    const D: BaseField<G> = <P as TwistedEdwardsParameters>::COEFF_D;
    const MONTGOMERY_A: BaseField<G> = <P as MontgomeryParameters>::COEFF_A;
    const MONTGOMERY_B: BaseField<G> = <P as MontgomeryParameters>::COEFF_B;

    pub fn encode(input: BaseField<G>) -> Result<(G, bool)> {
        ensure!(Self::D.legendre().is_qnr(), "D on the twisted Edwards curve must be a quadratic nonresidue");
        ensure!(!input.is_zero(), "Inputs to Elligator2 must be nonzero (inverses will fail)");

        let one = BaseField::<G>::one();

        // We define as convention for the input to be of high sign.
        let sign_high = input > input.neg();
        let input = if sign_high { input } else { input.neg() };

        // Compute the mapping from Fq to E(Fq) as a Montgomery element (u, v).
        let (u, v) = {
            // Compute the coefficients for the Weierstrass form: y^2 == x^3 + A * x^2 + B * x.
            let montgomery_b_inverse = Self::MONTGOMERY_B.inverse().unwrap();
            let a = Self::MONTGOMERY_A * montgomery_b_inverse;
            let b = montgomery_b_inverse.square();

            // Let ur2 = D * input^2;
            let ur2 = Self::D * input.square();
            // Verify 1 + ur^2 != 0.
            assert_ne!(one + ur2, BaseField::<G>::zero());
            // Verify A^2 * ur^2 != B(1 + ur^2)^2.
            assert_ne!(a.square() * ur2, b * (one + ur2).square());

            // Let v = -A / (1 + ur^2).
            let v = -a * (one + ur2).inverse().unwrap();

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
            let value = rhs.sqrt().unwrap();
            let y = match e {
                LegendreSymbol::Zero => BaseField::<G>::zero(),
                LegendreSymbol::QuadraticResidue => -value,
                LegendreSymbol::QuadraticNonResidue => value,
            };

            // Ensure (u, v) is a valid Weierstrass element on: y^2 == x^3 + A * x^2 + B * x
            assert_eq!(y.square(), rhs);

            // Convert the Weierstrass element (x, y) to Montgomery element (u, v).
            let u = x * Self::MONTGOMERY_B;
            let v = y * Self::MONTGOMERY_B;

            // Ensure (u, v) is a valid Montgomery element on: B * v^2 == u^3 + A * u^2 + u
            let u2 = u.square();
            assert_eq!(Self::MONTGOMERY_B * v.square(), (u2 * u) + (Self::MONTGOMERY_A * u2) + u);

            (u, v)
        };

        // Convert the Montgomery element (u, v) to the twisted Edwards element (x, y).
        let x = u * v.inverse().unwrap();
        let y = (u - one) * (u + one).inverse().unwrap();

        Ok((G::from_coordinates((x, y)), sign_high))
    }

    pub fn decode(group: G, sign_high: bool) -> Result<BaseField<G>> {
        ensure!(Self::D.legendre().is_qnr(), "D on the twisted Edwards curve must be a quadratic nonresidue");
        ensure!(!group.is_zero(), "Inputs to Elligator2 must be nonzero (inverses will fail)");

        // Compute the coefficients for the Weierstrass form: v^2 == u^3 + A * u^2 + B * u.
        let montgomery_b_inverse = Self::MONTGOMERY_B.inverse().unwrap();
        let a = Self::MONTGOMERY_A * montgomery_b_inverse;
        let b = montgomery_b_inverse.square();

        let x = group.to_x_coordinate();
        let y = group.to_y_coordinate();

        // Verify that x != -A.
        assert_ne!(x, -a);
        // Verify that if y is 0, then x is 0.
        if y.is_zero() {
            assert!(x.is_zero());
        }

        // Convert the twisted Edwards element (x, y) to the Weierstrass element (u, v)
        let (u_reconstructed, v_reconstructed) = {
            let one = BaseField::<G>::one();

            let numerator = one + y;
            let denominator = one - y;

            let u = numerator * denominator.inverse().unwrap();
            let v = numerator * (denominator * x).inverse().unwrap();

            // Ensure (u, v) is a valid Montgomery element on: B * v^2 == u^3 + A * u^2 + u
            let u2 = u.square();
            assert_eq!(Self::MONTGOMERY_B * v.square(), (u2 * u) + (Self::MONTGOMERY_A * u2) + u);

            let u = u * montgomery_b_inverse;
            let v = v * montgomery_b_inverse;

            // Ensure (u, v) is a valid Weierstrass element on: v^2 == u^3 + A * u^2 + B * u
            let u2 = u.square();
            assert_eq!(v.square(), (u2 * u) + (a * u2) + (b * u));

            (u, v)
        };

        let x = u_reconstructed;

        // Let u = D.
        let u = Self::D;
        // Verify -ux(x + A) is a residue.
        assert_eq!((-(u * x) * (x + a)).legendre(), LegendreSymbol::QuadraticResidue);

        let exists_in_sqrt_fq2 = v_reconstructed.square().sqrt().unwrap() == v_reconstructed;

        let element = match exists_in_sqrt_fq2 {
            // Let element = sqrt(-x / ((x + A) * u)).
            true => (-x * ((x + a) * u).inverse().unwrap()).sqrt().unwrap(),
            // Let element = sqrt(-(x + A) / ux)).
            false => ((-x - a) * (u * x).inverse().unwrap()).sqrt().unwrap(),
        };

        match sign_high {
            true => Ok(cmp::max(element, -element)),
            false => Ok(cmp::min(element, -element)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::edwards_bls12::{EdwardsAffine, EdwardsParameters};
    use snarkvm_utilities::{test_rng, UniformRand};

    pub(crate) const ITERATIONS: usize = 10000;

    #[test]
    fn test_encode_and_decode() {
        let rng = &mut test_rng();

        let mut high_ctr = 0usize;
        let mut low_ctr = 0usize;

        for _ in 0..ITERATIONS {
            let expected = UniformRand::rand(rng);

            let (encoded, sign_high) = Elligator2::<EdwardsAffine, EdwardsParameters>::encode(expected).unwrap();
            let decoded = Elligator2::<EdwardsAffine, EdwardsParameters>::decode(encoded, sign_high).unwrap();
            assert_eq!(expected, decoded);

            match sign_high {
                true => high_ctr += 1,
                false => low_ctr += 1,
            }
        }

        println!("high: {}, low: {}", high_ctr, low_ctr);
    }

    #[test]
    fn test_zero_fails() {
        let encode = Elligator2::<EdwardsAffine, EdwardsParameters>::encode(Zero::zero());
        assert!(encode.is_err());

        let decode = Elligator2::<EdwardsAffine, EdwardsParameters>::decode(Zero::zero(), true);
        assert!(decode.is_err());
        let decode = Elligator2::<EdwardsAffine, EdwardsParameters>::decode(Zero::zero(), false);
        assert!(decode.is_err());
    }
}
