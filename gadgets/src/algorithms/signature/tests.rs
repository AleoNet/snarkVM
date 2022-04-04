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

mod aleo {
    use crate::{
        algorithms::signature::AleoSignatureSchemeGadget,
        traits::{algorithms::SignatureGadget, alloc::AllocGadget, eq::EqGadget},
        Boolean,
    };
    use snarkvm_algorithms::{signature::AleoSignatureScheme, traits::SignatureScheme};
    use snarkvm_curves::{bls12_377::Fr, edwards_bls12::EdwardsParameters};
    use snarkvm_r1cs::{ConstraintSystem, TestConstraintSystem};
    use snarkvm_utilities::ToBits;

    use rand::SeedableRng;
    use rand_chacha::ChaChaRng;

    type TestSignatureScheme = AleoSignatureScheme<EdwardsParameters>;
    type TestSignatureSchemeGadget = AleoSignatureSchemeGadget<EdwardsParameters, Fr>;

    #[test]
    fn test_signature_verification() {
        let message = "Hi, I am an Aleo signature!".as_bytes().to_bits_le();
        let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

        let signature_scheme = TestSignatureScheme::setup("aleo_signature_verification_test");
        let private_key = signature_scheme.generate_private_key(rng);
        let public_key = signature_scheme.generate_public_key(&private_key);
        let signature = signature_scheme.sign(&private_key, &message, rng).unwrap();
        assert!(signature_scheme.verify(&public_key, &message, &signature).unwrap());

        let mut cs = TestConstraintSystem::<Fr>::new();

        let signature_scheme_gadget =
            TestSignatureSchemeGadget::alloc_constant(&mut cs.ns(|| "signature_scheme_gadget"), || {
                Ok(signature_scheme)
            })
            .unwrap();

        assert_eq!(cs.num_constraints(), 0);

        let public_key_gadget =
            <TestSignatureSchemeGadget as SignatureGadget<TestSignatureScheme, Fr>>::PublicKeyGadget::alloc(
                cs.ns(|| "alloc_public_key"),
                || Ok(public_key),
            )
            .unwrap();

        assert_eq!(cs.num_constraints(), 13);

        let message_gadget = message
            .iter()
            .enumerate()
            .map(|(i, bit)| Boolean::alloc(cs.ns(|| format!("alloc_message {i}")), || Ok(bit)).unwrap())
            .collect::<Vec<_>>();

        assert_eq!(cs.num_constraints(), 229);

        let signature_gadget =
            <TestSignatureSchemeGadget as SignatureGadget<TestSignatureScheme, Fr>>::SignatureGadget::alloc(
                cs.ns(|| "alloc_signature"),
                || Ok(signature),
            )
            .unwrap();

        assert_eq!(cs.num_constraints(), 235);

        let verification = signature_scheme_gadget
            .verify(cs.ns(|| "verify"), &public_key_gadget, &message_gadget, &signature_gadget)
            .unwrap();

        assert_eq!(cs.num_constraints(), 8881);

        verification.enforce_equal(cs.ns(|| "check_verification"), &Boolean::constant(true)).unwrap();

        if !cs.is_satisfied() {
            println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied());
    }

    #[test]
    fn failed_test_signature_verification() {
        let message = "Hi, I am an Aleo signature!".as_bytes().to_bits_le();
        let bad_message = "Bad Message".as_bytes().to_bits_le();
        let rng = &mut ChaChaRng::seed_from_u64(1231275789u64);

        let signature_scheme = TestSignatureScheme::setup("failed_aleo_signature_verification_test");
        let private_key = signature_scheme.generate_private_key(rng);
        let public_key = signature_scheme.generate_public_key(&private_key);
        let signature = signature_scheme.sign(&private_key, &message, rng).unwrap();

        assert!(signature_scheme.verify(&public_key, &message, &signature).unwrap());
        assert!(!signature_scheme.verify(&public_key, &bad_message, &signature).unwrap());

        let mut cs = TestConstraintSystem::<Fr>::new();

        let signature_scheme_gadget =
            TestSignatureSchemeGadget::alloc_constant(&mut cs.ns(|| "signature_scheme_gadget"), || {
                Ok(signature_scheme)
            })
            .unwrap();

        let public_key_gadget =
            <TestSignatureSchemeGadget as SignatureGadget<TestSignatureScheme, Fr>>::PublicKeyGadget::alloc(
                cs.ns(|| "alloc_public_key"),
                || Ok(public_key),
            )
            .unwrap();

        let bad_message_gadget = bad_message
            .iter()
            .enumerate()
            .map(|(i, bit)| Boolean::alloc(cs.ns(|| format!("alloc_message {i}")), || Ok(bit)).unwrap())
            .collect::<Vec<_>>();

        let signature_gadget =
            <TestSignatureSchemeGadget as SignatureGadget<TestSignatureScheme, Fr>>::SignatureGadget::alloc(
                cs.ns(|| "alloc_signature"),
                || Ok(signature),
            )
            .unwrap();

        let verification = signature_scheme_gadget
            .verify(cs.ns(|| "verify"), &public_key_gadget, &bad_message_gadget, &signature_gadget)
            .unwrap();

        verification.enforce_equal(cs.ns(|| "check_verification"), &Boolean::constant(false)).unwrap();

        if !cs.is_satisfied() {
            println!("which is unsatisfied: {:?}", cs.which_is_unsatisfied().unwrap());
        }
        assert!(cs.is_satisfied());
    }
}
