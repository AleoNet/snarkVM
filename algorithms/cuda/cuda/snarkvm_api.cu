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

#include <cuda.h>

#include "snarkvm.cu"

#ifndef __CUDA_ARCH__

// Lazy instantiation of snarkvm_t
class snarkvm_singleton_t {
    bool failed = false;
    snarkvm_t *snarkvm = nullptr;

public:
    snarkvm_singleton_t() {}
    ~snarkvm_singleton_t() {
        delete snarkvm;
        snarkvm = nullptr;
    }
    bool ok() {
        if (!failed && snarkvm == nullptr) {
            // SNP TODO: max domain size?
            snarkvm = new snarkvm_t(17);
            if (snarkvm == nullptr) {
                failed = true;
            }
        }
        return snarkvm != nullptr;
    }
    snarkvm_t* operator->() {
        assert (ok());
        return snarkvm;
    }
};
snarkvm_singleton_t snarkvm_g;
                                         
#ifndef __CUDA_ARCH__

extern "C" {
    RustError snarkvm_ntt(fr_t* inout, uint32_t lg_domain_size,
                          NTT::InputOutputOrder ntt_order, NTT::Direction ntt_direction,
                          NTT::Type ntt_type)
    {
        if (!snarkvm_g.ok()) {
            return RustError{cudaErrorMemoryAllocation};
        }
        return snarkvm_g->NTT(inout, inout, lg_domain_size, ntt_order,
                              ntt_direction, ntt_type);
    }

    RustError snarkvm_polymul(fr_t* out,
                              size_t pcount, fr_t** polynomials, size_t* plens,
                              size_t ecount, fr_t** evaluations, size_t* elens,
                              uint32_t lg_domain_size) {
        if (!snarkvm_g.ok()) {
            return RustError{cudaErrorMemoryAllocation};
        }
        return snarkvm_g->PolyMul(out,
                                  pcount, polynomials, plens,
                                  ecount, evaluations, elens,
                                  lg_domain_size);
    }

    RustError snarkvm_msm(point_t* out, const affine_t points[], size_t npoints,
                          const scalar_t scalars[], size_t ffi_affine_size) {
        if (!snarkvm_g.ok()) {
            return RustError{cudaErrorMemoryAllocation};
        }
        return snarkvm_g->MSM(out, points, npoints, scalars, ffi_affine_size);
    }
}
#endif // __CUDA_ARCH__

#endif
