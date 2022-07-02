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

impl<A: Aleo> Trace<A> {
    /// Returns `true` if the signature is valid, and `false` otherwise.
    ///
    /// Verifies (challenge == challenge') && (address == address') && (serial_numbers == serial_numbers') where:
    ///     challenge' := HashToScalar(r * G, pk_sig, pr_sig, caller, \[tvk, input IDs\])
    pub fn verify(&self) -> Boolean<A> {
        // Construct the input IDs as field elements.
        let input_ids = self.input_ids.iter().map(|input| input.to_fields()).collect::<Vec<_>>();

        // Construct the signature message as `[tvk, input IDs]`.
        let mut message = Vec::with_capacity(1 + input_ids.len());
        message.push(self.tvk.clone());
        message.extend(input_ids.into_iter().flatten());

        // Retrieve the challenge from the signature.
        let challenge = self.signature.challenge();
        // Retrieve the response from the signature.
        let response = self.signature.response();

        // Initialize a vector for the serial number checks.
        let mut check_sn = Vec::with_capacity(self.input_ids.len());

        // Verify each serial number is computed correctly.
        for input in self.input_ids.iter() {
            match input {
                InputID::Constant(..) | InputID::Public(..) | InputID::Private(..) => continue,
                InputID::Record(commitment, h, h_r, gamma, serial_number) => {
                    // Compute the generator `H` as `HashToGroup(commitment)`.
                    let candidate_h = A::hash_to_group_psd2(&[A::serial_number_domain(), commitment.clone()]);
                    // Compute `h_r` as `(challenge * gamma) + (response * H)`, equivalent to `r * H`.
                    let candidate_h_r = (gamma * challenge) + (&candidate_h * response);
                    // Compute `sn_nonce` as `HashToScalar(COFACTOR * gamma)`.
                    let sn_nonce =
                        A::hash_to_scalar_psd2(&[A::serial_number_domain(), gamma.mul_by_cofactor().to_x_coordinate()]);
                    // Compute `candidate_serial_number` as `Commit(commitment, serial_number_nonce)`.
                    let candidate_serial_number =
                        A::commit_bhp512(&(A::serial_number_domain(), commitment).to_bits_le(), &sn_nonce);

                    // Ensure the candidate H matches the expected H.
                    check_sn.push(
                        h.is_equal(&candidate_h)
                        // Ensure `h_r` matches.
                        & h_r.is_equal(&candidate_h_r)
                        // Ensure the candidate serial number matches the expected serial number.
                        & serial_number.is_equal(&candidate_serial_number),
                    );
                }
            }
        }

        // Verify the signature and serial numbers are valid.
        self.signature.verify(&self.caller, &message) & check_sn.iter().fold(Boolean::constant(true), |acc, x| acc & x)
    }
}

#[cfg(all(test, console))]
mod tests {
    use super::*;
    use crate::Circuit;
    use snarkvm_utilities::{test_crypto_rng, Uniform};

    use anyhow::Result;

    pub(crate) const ITERATIONS: usize = 50;

    fn check_verify(
        mode: Mode,
        num_constants: u64,
        num_public: u64,
        num_private: u64,
        num_constraints: u64,
    ) -> Result<()> {
        let rng = &mut test_crypto_rng();

        for i in 0..ITERATIONS {
            // Sample a random private key and address.
            let private_key = snarkvm_console_account::PrivateKey::<<Circuit as Environment>::Network>::new(rng)?;
            let caller = console::Address::try_from(&private_key)?;

            // Construct a program ID and function name.
            let program_id = console::ProgramID::from_str("token.aleo")?;
            let function_name = console::Identifier::from_str("transfer")?;

            // Construct two input records.
            let input_record = console::Record::from_str("{ owner: aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah.private, balance: 5u64.private, token_amount: 100u64.private }").unwrap();
            let input = console::StackValue::<<Circuit as Environment>::Network>::Record(input_record.clone());
            let inputs = vec![input.clone(), input.clone()];

            // Construct the input types.
            let input_types = vec![console::ValueType::Record(console::Identifier::from_str("token")?); 2];

            // Construct the request.
            let request = console::Request::new(caller, program_id, function_name, inputs);

            // Retrieve `sk_sig` and `pr_sig`.
            let sk_sig = private_key.sk_sig();
            let pr_sig = snarkvm_console_account::ComputeKey::try_from(&private_key)?.pr_sig();

            // Compute the trace by signing the request.
            let trace = console::Trace::sign(&request, &input_types, &sk_sig, &pr_sig, rng)?;
            assert!(trace.verify());

            // Inject the trace into a circuit.
            let trace = Trace::<Circuit>::new(mode, trace);

            Circuit::scope(format!("Trace {i}"), || {
                let candidate = trace.verify();
                assert!(candidate.eject_value());
                assert_scope!(<=num_constants, num_public, num_private, num_constraints);
            })
        }
        Ok(())
    }

    #[test]
    fn test_sign_and_verify_constant() -> Result<()> {
        check_verify(Mode::Constant, 27867, 0, 0, 0)
    }

    #[test]
    fn test_sign_and_verify_public() -> Result<()> {
        check_verify(Mode::Public, 19338, 0, 28084, 28140)
    }

    #[test]
    fn test_sign_and_verify_private() -> Result<()> {
        check_verify(Mode::Private, 19338, 0, 28084, 28140)
    }
}
