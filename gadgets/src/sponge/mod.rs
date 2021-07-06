use crate::fields::FpGadget;
use snarkvm_fields::PrimeField;
use snarkvm_r1cs::{ConstraintSystem, SynthesisError};
use snarkvm_sponge::CryptographicSponge;

/// The interface for a cryptographic sponge constraints on field `CF`.
/// A sponge can `absorb` or take in inputs and later `squeeze` or output bytes or field elements.
/// The outputs are dependent on previous `absorb` and `squeeze` calls.
pub trait CryptographicSpongeVar<CF: PrimeField, S: CryptographicSponge<CF>>: Clone {
    /// Parameters used by the sponge.
    type Parameters;

    /// Initialize a new instance of the sponge.
    fn new<CS: ConstraintSystem<CF>>(cs: CS, params: &Self::Parameters) -> Self;

    /// Absorb an input into the sponge.
    fn absorb<'a, CS: ConstraintSystem<CF>, I: Iterator<Item = &'a FpGadget<CF>>>(
        &mut self,
        cs: CS,
        input: I,
    ) -> Result<(), SynthesisError>;

    /// Squeeze `num_elements` field elements from the sponge.
    fn squeeze_field_elements<CS: ConstraintSystem<CF>>(
        &mut self,
        cs: CS,
        num_elements: usize,
    ) -> Result<Vec<FpGadget<CF>>, SynthesisError>;
}
