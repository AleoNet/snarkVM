#!/bin/bash

nvcc ./asm_cuda.cu -ptx -rdc=true -o ./asm_cuda.release.ptx
nvcc ./blst_377_ops.cu -ptx -rdc=true -o ./blst_377_ops.release.ptx
nvcc ./msm.cu -ptx -rdc=true -o ./msm.release.ptx

nvcc ./asm_cuda.cu --device-debug -ptx -rdc=true -o ./asm_cuda.debug.ptx
nvcc ./blst_377_ops.cu --device-debug -ptx -rdc=true -o ./blst_377_ops.debug.ptx
nvcc ./msm.cu --device-debug -ptx -rdc=true -o ./msm.debug.ptx
nvcc ./tests.cu --device-debug -ptx -rdc=true -o ./tests.debug.ptx
