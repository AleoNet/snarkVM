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

use crate::prf::{Blake2Xs, ALEO_PERSONA};
use snarkvm_curves::AffineCurve;

const ZERO_OFFSET: u32 = 0;
const ONE_OFFSET: u32 = 1;
const TWO_OFFSET: u32 = 2;
const THREE_OFFSET: u32 = 3;

#[inline]
pub fn try_hash_to_curve<G: AffineCurve, const FIELD_BITS: u32, const XOF_DIGEST_LENGTH: u16>(
    input: &str,
) -> Option<(G, u32)> {
    // Try incrementing counter `k` FIELD_BITS times.
    for k in 0..FIELD_BITS {
        // Construct a new message.
        let message = format!("{} in {}", input, k);

        // Output the generator if a valid generator was found.
        if let Some(g) = hash_to_curve::<G, FIELD_BITS, XOF_DIGEST_LENGTH>(&message) {
            println!("{}", message);
            return Some((g, k));
        }
    }
    None
}

#[inline]
pub fn hash_to_curve<G: AffineCurve, const FIELD_BITS: u32, const XOF_DIGEST_LENGTH: u16>(input: &str) -> Option<G> {
    // The number of Blake2Xs invocations needed.
    let num_rounds: u16 = match FIELD_BITS % 256 > 0 {
        true => ((FIELD_BITS / 256) + 1) as u16,
        false => (FIELD_BITS / 256) as u16,
    };

    // Compute the digest for deriving the generator.
    let mut digest = Vec::with_capacity(XOF_DIGEST_LENGTH as usize);
    for offset in 0..=num_rounds {
        digest.extend_from_slice(&match offset {
            0 => Blake2Xs::evaluate::<ZERO_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            1 => Blake2Xs::evaluate::<ONE_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            2 => Blake2Xs::evaluate::<TWO_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            3 => Blake2Xs::evaluate::<THREE_OFFSET, XOF_DIGEST_LENGTH, ALEO_PERSONA>(input.as_bytes()),
            _ => unimplemented!("hash_to_curve supports up to a 1024-bit base field element"),
        });
    }

    // Attempt to use the digest to derive a generator.
    G::from_random_bytes(&digest).and_then(|g| {
        let g = g.mul_by_cofactor();
        match !g.is_zero() {
            true => return Some(g),
            false => None,
        }
    })
}

#[cfg(test)]
mod bls12_377 {
    use crate::hash_to_curve::{hash_to_curve, try_hash_to_curve};
    use snarkvm_curves::{
        bls12_377::{FqParameters, G1Affine, G2Affine},
        AffineCurve,
    };
    use snarkvm_fields::FieldParameters;

    const FIELD_BITS: u32 = FqParameters::MODULUS_BITS;

    #[test]
    fn hash_bls12_377_g1() {
        let g1 = hash_to_curve::<G1Affine, FIELD_BITS, 512>("Aleo BLS12-377 G1 in 2").unwrap();
        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(
            g1.x.to_string(),
            "158156260823117507888693535084466232824779812809970945470560141963154412482435784320318186163184859520169843530551"
        );
        assert_eq!(
            g1.y.to_string(),
            "101649641885220841928061137108907365288027337468958757307620986090692360142741358761135939634151351398134601677025"
        );
        assert_eq!(
            try_hash_to_curve::<G1Affine, FIELD_BITS, 512>("Aleo BLS12-377 G1"),
            Some((g1, 2))
        );
    }

    #[test]
    fn hash_bls12_377_g2() {
        let g2 = hash_to_curve::<G2Affine, FIELD_BITS, 512>("Aleo BLS12-377 G2 in 0").unwrap();
        assert!(g2.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(
            g2.x.to_string(),
            "Fp2(18530967594235566243335187101752570107616176349552784968178098996818868750252111351392075324115454717813888945791 + 249109238597864858227740027174673999737378771274637856066753519982906549035341230102237437984449583493201730309992 * u)"
        );
        assert_eq!(
            g2.y.to_string(),
            "Fp2(162411681306238058413572478072422455473006141666469347219463629164083502715167424891268870041372045373590873694831 + 242659755380625277054368746168481273389655769841276332694767846852600636897945523549638958523260502082430026303549 * u)"
        );
        assert_eq!(
            try_hash_to_curve::<G2Affine, FIELD_BITS, 512>("Aleo BLS12-377 G2"),
            Some((g2, 0))
        );
    }
}

#[cfg(test)]
mod bw6_761 {
    use crate::hash_to_curve::{hash_to_curve, try_hash_to_curve};
    use snarkvm_curves::{
        bw6_761::{FqParameters, G1Affine, G2Affine},
        AffineCurve,
    };
    use snarkvm_fields::FieldParameters;

    const FIELD_BITS: u32 = FqParameters::MODULUS_BITS;

    #[test]
    fn hash_bw6_761_g1() {
        let g1 = hash_to_curve::<G1Affine, FIELD_BITS, 768>("Aleo BW6-761 G1 in 6").unwrap();
        assert!(g1.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(
            g1.x.to_string(),
            "548300277143208370470678695366266429839120799927220954217122412131700072565385886272330413155172409119755953304536074890149359412851408456414505595462512752071492788194267343564981261358941753195544463428712608241091867757122460"
        );
        assert_eq!(
            g1.y.to_string(),
            "3317472076756963306110108609744156196308178143114799958012980985496220654686731782787499145400398246050358757683997715518181197214027285759025659330708904762639837257598196509175335127695930298616567045490708432441379668097317972"
        );
        assert_eq!(
            try_hash_to_curve::<G1Affine, FIELD_BITS, 768>("Aleo BW6-761 G1"),
            Some((g1, 6))
        );
    }

    #[test]
    fn hash_bw6_761_g2() {
        let g2 = hash_to_curve::<G2Affine, FIELD_BITS, 768>("Aleo BW6-761 G2 in 2").unwrap();
        assert!(g2.is_in_correct_subgroup_assuming_on_curve());
        assert_eq!(
            g2.x.to_string(),
            "12396641805492461664047944547716626246622726413716325514578855015708751941073354605391144730949906058792699340873351761792275567434439857256502535718512012900825516349253359648697192702793852676897460477790268766996191561426115"
        );
        assert_eq!(
            g2.y.to_string(),
            "3307524539084980175348192287168406817851662089289532346813191207846857431628300288777230178426528997214653383965949568784001180902638452916442590352134990654138684202694553699651807581643537139768612814360134519690660810904199476"
        );
        assert_eq!(
            try_hash_to_curve::<G2Affine, FIELD_BITS, 768>("Aleo BW6-761 G2"),
            Some((g2, 2))
        );
    }
}
