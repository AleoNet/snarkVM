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

#[allow(unused_imports)]
use blst::*;

use core::ffi::c_void;
sppark::cuda_error!();

#[repr(C)]
pub enum NTTInputOutputOrder {
    NN = 0,
    NR = 1,
    RN = 2,
    RR = 3,
}

#[repr(C)]
pub enum NTTDirection {
    Forward = 0,
    Inverse = 1,
}

#[repr(C)]
pub enum NTTType {
    Standard = 0,
    Coset = 1,
}

extern "C" {
    fn snarkvm_ntt(
        inout: *mut core::ffi::c_void,
        lg_domain_size: u32,
        ntt_order: NTTInputOutputOrder,
        ntt_direction: NTTDirection,
        ntt_type: NTTType,
    ) -> cuda::Error;

    fn snarkvm_polymul(
        out: *mut core::ffi::c_void,
        pcount: usize,
        polynomials: *const core::ffi::c_void,
        plens: *const core::ffi::c_void,
        ecount: usize,
        evaluations: *const core::ffi::c_void,
        elens: *const core::ffi::c_void,
        lg_domain_size: u32,
    ) -> cuda::Error;

    fn snarkvm_msm(
        out: *mut c_void,
        points_with_infinity: *const c_void,
        npoints: usize,
        scalars: *const c_void,
        ffi_affine_sz: usize,
    ) -> cuda::Error;
}

///////////////////////////////////////////////////////////////////////////////
// Rust functions
///////////////////////////////////////////////////////////////////////////////

/// Compute an in-place NTT on the input data.
#[allow(non_snake_case)]
pub fn NTT<T>(
    domain_size: usize,
    inout: &mut [T],
    ntt_order: NTTInputOutputOrder,
    ntt_direction: NTTDirection,
    ntt_type: NTTType,
) -> Result<(), cuda::Error> {
    if (domain_size & (domain_size - 1)) != 0 {
        panic!("domain_size is not power of 2");
    }
    let lg_domain_size = domain_size.trailing_zeros();

    let err = unsafe {
        snarkvm_ntt(inout.as_mut_ptr() as *mut core::ffi::c_void, lg_domain_size, ntt_order, ntt_direction, ntt_type)
    };

    if err.code != 0 {
        return Err(err);
    }
    Ok(())
}

/// Compute a polynomial multiply
pub fn polymul<T: std::clone::Clone>(
    domain: usize,
    polynomials: &Vec<Vec<T>>,
    evaluations: &Vec<Vec<T>>,
    zero: &T,
) -> Result<Vec<T>, cuda::Error> {
    let initial_domain_size = domain;
    if (initial_domain_size & (initial_domain_size - 1)) != 0 {
        panic!("domain_size is not power of 2");
    }

    let lg_domain_size = initial_domain_size.trailing_zeros();

    let mut pptrs = Vec::new();
    let mut plens = Vec::new();
    for polynomial in polynomials {
        pptrs.push(polynomial.as_ptr() as *const core::ffi::c_void);
        plens.push(polynomial.len());
    }
    let mut eptrs = Vec::new();
    let mut elens = Vec::new();
    for evaluation in evaluations {
        eptrs.push(evaluation.as_ptr() as *const core::ffi::c_void);
        elens.push(evaluation.len());
    }

    let mut out = Vec::new();
    out.resize(initial_domain_size, zero.clone());
    let err = unsafe {
        snarkvm_polymul(
            out.as_mut_ptr() as *mut core::ffi::c_void,
            pptrs.len(),
            pptrs.as_ptr() as *const core::ffi::c_void,
            plens.as_ptr() as *const core::ffi::c_void,
            eptrs.len(),
            eptrs.as_ptr() as *const core::ffi::c_void,
            elens.as_ptr() as *const core::ffi::c_void,
            lg_domain_size,
        )
    };

    if err.code != 0 {
        return Err(err);
    }
    Ok(out)
}

/// Compute a multi-scalar multiplication
pub fn msm<Affine, Projective, Scalar>(points: &[Affine], scalars: &[Scalar]) -> Result<Projective, cuda::Error> {
    let npoints = scalars.len();
    if npoints > points.len() {
        panic!("length mismatch {} points < {} scalars", npoints, scalars.len())
    }
    #[allow(clippy::uninit_assumed_init)]
    let mut ret: Projective = unsafe { std::mem::MaybeUninit::uninit().assume_init() };
    let err = unsafe {
        snarkvm_msm(
            &mut ret as *mut _ as *mut c_void,
            points as *const _ as *const c_void,
            npoints,
            scalars as *const _ as *const c_void,
            std::mem::size_of::<Affine>(),
        )
    };
    if err.code != 0 {
        return Err(err);
    }
    Ok(ret)
}
