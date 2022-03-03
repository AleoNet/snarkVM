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

use core::fmt::Debug;

/// A macro for computing ceil(log2(x))+1 for a field element x
#[macro_export]
macro_rules! overhead {
    ($x:expr) => {{
        use snarkvm_utilities::ToBits;
        let num = $x;
        let num_bits = num.to_repr().to_bits_be();
        let mut skipped_bits = 0;
        for b in num_bits.iter() {
            if *b == false {
                skipped_bits += 1;
            } else {
                break;
            }
        }

        let mut is_power_of_2 = true;
        for b in num_bits.iter().skip(skipped_bits + 1) {
            if *b == true {
                is_power_of_2 = false;
            }
        }

        if is_power_of_2 { num_bits.len() - skipped_bits } else { num_bits.len() - skipped_bits + 1 }
    }};
}

/// Parameters for a specific `NonNativeFieldVar` instantiation
#[derive(Clone, Debug)]
pub struct NonNativeFieldParams {
    /// The number of limbs (`BaseField` elements) used to represent a `TargetField` element. Highest limb first.
    pub num_limbs: usize,

    /// The number of bits of the limb
    pub bits_per_limb: usize,
}

/// Obtain the parameters from a `ConstraintSystem`'s cache or generate a new one
#[must_use]
pub const fn get_params(
    target_field_size: usize,
    base_field_size: usize,
    optimization_type: OptimizationType,
) -> NonNativeFieldParams {
    let (num_of_limbs, limb_size) = find_parameters(base_field_size, target_field_size, optimization_type);
    NonNativeFieldParams { num_limbs: num_of_limbs, bits_per_limb: limb_size }
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
