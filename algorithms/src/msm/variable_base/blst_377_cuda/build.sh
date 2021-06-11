#!/bin/bash

nvcc ./asm_cuda.cu ./blst_377_ops.cu ./msm.cu -arch=compute_70 -code=sm_70 -dlink -fatbin -o ./kernel