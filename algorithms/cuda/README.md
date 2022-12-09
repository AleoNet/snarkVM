# snarkvm-cuda

[![Crates.io](https://img.shields.io/crates/v/snarkvm-cuda.svg?color=neon)](https://crates.io/crates/snarkvm-cuda)
[![Authors](https://img.shields.io/badge/authors-Aleo-orange.svg)](https://aleo.org)
[![License](https://img.shields.io/badge/License-GPLv3-blue.svg)](./LICENSE.md)

## Build Requirements

- Cuda `sm_70` or later
- [Cuda Toolkit (nvcc)](https://docs.nvidia.com/cuda/index.html#installation-guides)

## Usage Guide

- Simply enable the `cuda` feature in your command or snarkVM dependency

### Example

```
cd snarkVM/algorithms
cargo bench --bench variable_base --features "cuda"
```

or

```
[dependencies.snarkvm]
version = "<latest_version>"
features = ["cuda"]
```
