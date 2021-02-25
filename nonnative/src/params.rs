use crate::NonNativeFieldParams;

/// Obtain the parameters from a `ConstraintSystem`'s cache or generate a new one
#[must_use]
pub const fn get_params(
    target_field_size: usize,
    base_field_size: usize,
    optimization_type: OptimizationType,
) -> NonNativeFieldParams {
    let (num_of_limbs, limb_size) = find_parameters(base_field_size, target_field_size, optimization_type);
    NonNativeFieldParams {
        num_limbs: num_of_limbs,
        bits_per_limb: limb_size,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// The type of optimization target for the parameters searching
pub enum OptimizationType {
    /// Optimized for constraints
    Constraints,
    /// Optimized for weight
    Weight,
}

/// A function to search for parameters for nonnative field gadgets
pub const fn find_parameters(
    base_field_prime_length: usize,
    target_field_prime_bit_length: usize,
    optimization_type: OptimizationType,
) -> (usize, usize) {
    let mut found = false;
    let mut min_cost = 0usize;
    let mut min_cost_limb_size = 0usize;
    let mut min_cost_num_of_limbs = 0usize;

    let surfeit = 10;
    let mut max_limb_size = (base_field_prime_length - 1 - surfeit - 1) / 2 - 1;
    if max_limb_size > target_field_prime_bit_length {
        max_limb_size = target_field_prime_bit_length;
    }
    let mut limb_size = 1;

    while limb_size <= max_limb_size {
        let num_of_limbs = (target_field_prime_bit_length + limb_size - 1) / limb_size;

        let group_size = (base_field_prime_length - 1 - surfeit - 1 - 1 - limb_size + limb_size - 1) / limb_size;
        let num_of_groups = (2 * num_of_limbs - 1 + group_size - 1) / group_size;

        let mut this_cost = 0;

        match optimization_type {
            OptimizationType::Constraints => {
                this_cost += 2 * num_of_limbs - 1;
            }
            OptimizationType::Weight => {
                this_cost += 6 * num_of_limbs * num_of_limbs;
            }
        };

        match optimization_type {
            OptimizationType::Constraints => {
                this_cost += target_field_prime_bit_length; // allocation of k
                this_cost += target_field_prime_bit_length + num_of_limbs; // allocation of r
                //this_cost += 2 * num_of_limbs - 1; // compute kp
                this_cost += num_of_groups + (num_of_groups - 1) * (limb_size * 2 + surfeit) + 1;
                // equality check
            }
            OptimizationType::Weight => {
                this_cost += target_field_prime_bit_length * 3 + target_field_prime_bit_length; // allocation of k
                this_cost += target_field_prime_bit_length * 3 + target_field_prime_bit_length + num_of_limbs; // allocation of r
                this_cost += num_of_limbs * num_of_limbs + 2 * (2 * num_of_limbs - 1); // compute kp
                this_cost += num_of_limbs
                    + num_of_groups
                    + 6 * num_of_groups
                    + (num_of_groups - 1) * (2 * limb_size + surfeit) * 4
                    + 2; // equality check
            }
        };

        if !found || this_cost < min_cost {
            found = true;
            min_cost = this_cost;
            min_cost_limb_size = limb_size;
            min_cost_num_of_limbs = num_of_limbs;
        }

        limb_size += 1;
    }

    (min_cost_num_of_limbs, min_cost_limb_size)
}
