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
use snarkvm_utilities::{to_bytes_le, FromBytes, ToBytes};

use anyhow::{bail, Result};
use core::{cmp, marker::PhantomData, ops::Neg};

type BaseField<G> = <G as AffineCurve>::BaseField;

pub struct Elligator2<
    G: AffineCurve,
    P: MontgomeryParameters<BaseField = BaseField<G>> + TwistedEdwardsParameters<BaseField = BaseField<G>>,
>(PhantomData<(G, P)>);

impl<
    G: AffineCurve,
    P: MontgomeryParameters<BaseField = BaseField<G>> + TwistedEdwardsParameters<BaseField = BaseField<G>>,
> Elligator2<G, P>
{
    const A: BaseField<G> = <P as MontgomeryParameters>::COEFF_A;
    const B: BaseField<G> = <P as MontgomeryParameters>::COEFF_B;
    const D: BaseField<G> = <P as TwistedEdwardsParameters>::COEFF_D;

    pub fn encode(input: BaseField<G>) -> Result<(G, bool)> {
        // Verify D is a quadratic nonresidue.
        assert!(Self::D.legendre().is_qnr());

        // // The input base field must be nonzero, otherwise inverses will fail.
        // if input.is_zero() {
        //     return Err(EncodingError::InputMustBeNonzero);
        // }

        let one = BaseField::<G>::one();

        // We define as convention for the input to be of high sign.
        let sign_high = input > input.neg();
        let input = if sign_high { input } else { input.neg() };

        // Compute the mapping from Fq to E(Fq) as a Weierstrass element (u, v).
        let (u, v) = {
            // Compute the coefficients for the Weierstrass form: y^2 == x^3 + A * x^2 + B * x.
            let a = Self::A * &Self::B.inverse().unwrap();
            let b = one * &Self::B.square().inverse().unwrap();

            // Let ur2 = D * input^2;
            let ur2 = Self::D * input.square();
            // Verify 1 + ur^2 != 0.
            assert_ne!(one + &ur2, BaseField::<G>::zero());
            // Verify A^2 * ur^2 != B(1 + ur^2)^2.
            assert_ne!(a.square() * &ur2, (one + &ur2).square() * &b);

            // Let v = -A / (1 + ur^2).
            let v = (one + &ur2).inverse().unwrap() * &(-a);

            // Let e = legendre(v^3 + Av^2 + Bv).
            let v2 = v.square();
            let v3 = v2 * &v;
            let av2 = a.clone() * &v2;
            let bv = b.clone() * &v;
            let e = (v3 + &(av2 + &bv)).legendre();

            // Let x = ev - ((1 - e) * A/2).
            let x = match e {
                LegendreSymbol::Zero => -a * BaseField::<G>::half(),
                LegendreSymbol::QuadraticResidue => v,
                LegendreSymbol::QuadraticNonResidue => (-v) - &a,
            };

            // Let y = -e * sqrt(x^3 + Ax^2 + Bx).
            let x2 = x.square();
            let x3 = x2 * &x;
            let ax2 = a.clone() * &x2;
            let bx = b.clone() * &x;
            let value = (x3 + &(ax2 + &bx)).sqrt().unwrap();
            let y = match e {
                LegendreSymbol::Zero => BaseField::<G>::zero(),
                LegendreSymbol::QuadraticResidue => -value,
                LegendreSymbol::QuadraticNonResidue => value,
            };

            // Ensure (u, v) is a valid Weierstrass element on: y^2 == x^3 + A * x^2 + B * x
            let x2 = x.square();
            let x3 = x2 * &x;
            assert_eq!(y.square(), x3 + &(a * &x2) + &(b * &x));

            (x, y)
        };

        // Convert the Weierstrass element (u, v) to Montgomery element (s, t).
        let (s, t) = {
            let s = u * Self::B;
            let t = v * Self::B;

            // Ensure (s, t) is a valid Montgomery element on: B * t^2 == s^3 + A * s^2 + s
            let s2 = s.square();
            let s3 = s2 * &s;
            assert_eq!(Self::B * t.square(), s3 + &(Self::A * &s2) + &s);

            (s, t)
        };

        // Convert the Montgomery element (s, t) to the twisted Edwards element (x, y).
        let x = s * &t.inverse().unwrap();
        let y = (s - &one) * (s + one).inverse().unwrap();

        Ok((G::read_le(&to_bytes_le![x, y]?[..])?, sign_high))
    }

    pub fn decode(group: G, sign_high: bool) -> Result<BaseField<G>> {
        // // The input group element must be nonzero, otherwise inverses will fail.
        // if group_element.is_zero() {
        //     return Err(EncodingError::InputMustBeNonzero);
        // }

        let x = group.to_x_coordinate();
        let y = group.to_y_coordinate();

        let one = BaseField::<G>::one();

        // Compute the parameters for the Weierstrass form: v^2 == u^3 + A * u^2 + B * u.
        let a = Self::A * &Self::B.inverse().unwrap();
        let b = one * &Self::B.square().inverse().unwrap();

        // Convert the twisted Edwards element (x, y) to the Weierstrass element (u, v)
        let (u_reconstructed, v_reconstructed) = {
            let numerator = one + &y;
            let denominator = one - &y;

            let u = numerator.clone() * &(denominator.inverse().unwrap());
            let v = numerator * &((denominator * &x).inverse().unwrap());

            // Ensure (u, v) is a valid Montgomery element on: B * v^2 == u^3 + A * u^2 + u
            let u2 = u.square();
            let u3 = u2 * &u;
            assert_eq!(Self::B * v.square(), u3 + &(Self::A * &u2) + &u);

            let u = u * &Self::B.inverse().unwrap();
            let v = v * &Self::B.inverse().unwrap();

            // Ensure (u, v) is a valid Weierstrass element.
            {
                // Enforce v^2 == u^3 + A * u^2 + B * u
                let v2 = v.square();
                let u2 = u.square();
                let u3 = u2 * &u;
                assert_eq!(v2, u3 + &(a * &u2) + &(b * &u));
            }

            (u, v)
        };

        let x = u_reconstructed;

        // Let u = D.
        let u = Self::D;

        {
            // Verify u is a quadratic nonresidue.
            #[cfg(debug_assertions)]
            assert!(u.legendre().is_qnr());

            // Verify that x != -A.
            assert_ne!(x, -a);

            // Verify that if y is 0, then x is 0.
            if y.is_zero() {
                assert!(x.is_zero());
            }

            // Verify -ux(x + A) is a residue.
            assert_eq!((-(u * &x) * &(x + &a)).legendre(), LegendreSymbol::QuadraticResidue);
        }

        let exists_in_sqrt_fq2 = v_reconstructed.square().sqrt().unwrap() == v_reconstructed;

        let element = if exists_in_sqrt_fq2 {
            // Let value = sqrt(-x / ((x + A) * u)).
            let numerator = -x;
            let denominator = (x + &a) * &u;
            (numerator * &denominator.inverse().unwrap()).sqrt().unwrap()
        } else {
            // Let value2 = sqrt(-(x + A) / ux)).
            let numerator = -x - &a;
            let denominator = x * &u;
            (numerator * &denominator.inverse().unwrap()).sqrt().unwrap()
        };

        let element = if sign_high { cmp::max(element, -element) } else { cmp::min(element, -element) };

        #[cfg(debug_assertions)]
        assert!(Self::encode(element)?.0 == group);

        Ok(element)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_curves::edwards_bls12::{EdwardsAffine, EdwardsParameters};
    use snarkvm_utilities::{test_rng, UniformRand};

    pub(crate) const ITERATIONS: usize = 10000;

    #[test]
    fn test_elligator2_encode_decode() {
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

    // #[test]
    // fn test_elligator2_zero() {
    //     let encode = Elligator2::<EdwardsAffine, EdwardsParameters>::encode(&Zero::zero());
    //     assert!(encode.is_err());
    //
    //     let decode = Elligator2::<EdwardsAffine, EdwardsParameters>::decode(&EdwardsAffine::zero(), false);
    //     assert!(decode.is_err());
    // }
}
