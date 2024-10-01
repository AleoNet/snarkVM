// Copyright 2024 Aleo Network Foundation
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:

// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use snarkvm_fields::{
    Fp2Parameters,
    field,
    fp6_3over2::{Fp6, Fp6Parameters},
};
use snarkvm_utilities::biginteger::BigInteger384;

use crate::bls12_377::{Fq, Fq2, Fq2Parameters};

pub type Fq6 = Fp6<Fq6Parameters>;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Fq6Parameters;

impl Fp6Parameters for Fq6Parameters {
    type Fp2Params = Fq2Parameters;

    const FROBENIUS_COEFF_FP6_C1: [Fq2; 6] = [
        // Fp2::NONRESIDUE^(((q^0) - 1) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x2cdffffffffff68,
                    0x51409f837fffffb1,
                    0x9f7db3a98a7d3ff2,
                    0x7b4e97b76e7c6305,
                    0x4cf495bf803c84e8,
                    0x8d6661e2fdf49a,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^(((q^1) - 1) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x5892506da58478da,
                    0x133366940ac2a74b,
                    0x9b64a150cdf726cf,
                    0x5cc426090a9c587e,
                    0x5cf848adfdcd640c,
                    0x4702bf3ac02380,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^(((q^2) - 1) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0xdacd106da5847973,
                    0xd8fe2454bac2a79a,
                    0x1ada4fd6fd832edc,
                    0xfb9868449d150908,
                    0xd63eb8aeea32285e,
                    0x167d6a36f873fd0,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^(((q^3) - 1) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x823ac00000000099,
                    0xc5cabdc0b000004f,
                    0x7f75ae862f8c080d,
                    0x9ed4423b9278b089,
                    0x79467000ec64c452,
                    0x120d3e434c71c50,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^(((q^4) - 1) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x2c766f925a7b8727,
                    0x3d7f6b0253d58b5,
                    0x838ec0deec122131,
                    0xbd5eb3e9f658bb10,
                    0x6942bd126ed3e52e,
                    0x1673786dd04ed6a,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^(((q^5) - 1) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0xaa3baf925a7b868e,
                    0x3e0d38ef753d5865,
                    0x4191258bc861923,
                    0x1e8a71ae63e00a87,
                    0xeffc4d11826f20dc,
                    0x4663a2a83dd119,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
    ];
    const FROBENIUS_COEFF_FP6_C2: [Fq2; 6] = [
        // Fp2::NONRESIDUE^((2*(q^0) - 2) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x2cdffffffffff68,
                    0x51409f837fffffb1,
                    0x9f7db3a98a7d3ff2,
                    0x7b4e97b76e7c6305,
                    0x4cf495bf803c84e8,
                    0x8d6661e2fdf49a,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^((2*(q^1) - 2) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0xdacd106da5847973,
                    0xd8fe2454bac2a79a,
                    0x1ada4fd6fd832edc,
                    0xfb9868449d150908,
                    0xd63eb8aeea32285e,
                    0x167d6a36f873fd0,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^((2*(q^2) - 2) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x2c766f925a7b8727,
                    0x3d7f6b0253d58b5,
                    0x838ec0deec122131,
                    0xbd5eb3e9f658bb10,
                    0x6942bd126ed3e52e,
                    0x1673786dd04ed6a,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^((2*(q^3) - 2) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x2cdffffffffff68,
                    0x51409f837fffffb1,
                    0x9f7db3a98a7d3ff2,
                    0x7b4e97b76e7c6305,
                    0x4cf495bf803c84e8,
                    0x8d6661e2fdf49a,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^((2*(q^4) - 2) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0xdacd106da5847973,
                    0xd8fe2454bac2a79a,
                    0x1ada4fd6fd832edc,
                    0xfb9868449d150908,
                    0xd63eb8aeea32285e,
                    0x167d6a36f873fd0,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
        // Fp2::NONRESIDUE^((2*(q^5) - 2) / 3)
        field!(
            Fq2,
            field!(
                Fq,
                BigInteger384([
                    0x2c766f925a7b8727,
                    0x3d7f6b0253d58b5,
                    0x838ec0deec122131,
                    0xbd5eb3e9f658bb10,
                    0x6942bd126ed3e52e,
                    0x1673786dd04ed6a,
                ])
            ),
            field!(Fq, BigInteger384([0x0, 0x0, 0x0, 0x0, 0x0, 0x0])),
        ),
    ];
    /// NONRESIDUE = U
    const NONRESIDUE: Fq2 = field!(
        Fq2,
        field!(Fq, BigInteger384([0, 0, 0, 0, 0, 0])),
        field!(
            Fq,
            BigInteger384([
                202099033278250856u64,
                5854854902718660529u64,
                11492539364873682930u64,
                8885205928937022213u64,
                5545221690922665192u64,
                39800542322357402u64,
            ])
        ),
    );

    #[inline(always)]
    fn mul_fp2_by_nonresidue(fe: &Fq2) -> Fq2 {
        // Karatsuba multiplication with constant other = u.
        let c0 = Fq2Parameters::mul_fp_by_nonresidue(&fe.c1);
        let c1 = fe.c0;
        field!(Fq2, c0, c1)
    }
}

#[cfg(test)]
mod test {
    use snarkvm_fields::{One, Zero};
    use snarkvm_utilities::rand::{TestRng, Uniform};

    use super::*;

    #[test]
    fn test_fq2_mul_nonresidue() {
        let mut rng = TestRng::default();

        let nqr = Fq2::new(Fq::zero(), Fq::one());
        println!("One: {:?}", Fq::one());

        for _ in 0..1000 {
            let mut a = Fq2::rand(&mut rng);
            let mut b = a;
            a *= &Fq6Parameters::NONRESIDUE;
            b *= &nqr;

            assert_eq!(a, b);
        }
    }
}
