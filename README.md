<h1 align="center">snarkVM</h1>

<p align="center">
    <a href="https://circleci.com/gh/AleoHQ/snarkVM"><img src="https://circleci.com/gh/AleoHQ/snarkVM.svg?style=svg&circle-token=6e9ad6d39d95350544f352d34e0e5c62ef54db26"></a>
    <a href="https://codecov.io/gh/AleoHQ/snarkVM"><img src="https://codecov.io/gh/AleoHQ/snarkVM/branch/master/graph/badge.svg?token=cck8tS9HpO"/></a>
    <a href="https://discord.gg/jgH5wkwCtf"><img src="https://img.shields.io/discord/700454073459015690?logo=discord"/></a>
</p>

## Table of Contents

* [1. Overview](#1-overview)
* [2. Build Guide](#2-build-guide)
* [3. Usage Guide](#3-usage-guide)

## 1. Overview

** ATTENTION: This codebase is in active development. **

For more information, visit [Welcome to Aleo](https://github.com/AleoHQ/welcome) to get started.

## 2. Build Guide

### 2.1 Install Rust

We recommend installing Rust using [rustup](https://www.rustup.rs/). You can install `rustup` as follows:

- macOS or Linux:
  ```bash
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
  ```

- Windows (64-bit):  
  
  Download the [Windows 64-bit executable](https://win.rustup.rs/x86_64) or
  [Windows 32-bit executable](https://win.rustup.rs/i686) and follow the on-screen instructions.

### 2.2a Build from Crates.io

We recommend installing `snarkvm` this way. In your terminal, run:

```bash
cargo install snarkvm
```

Now to use `snarkvm`, in your terminal, run:
```bash
snarkvm
```
 
### 2.2b Build from Source Code

Alternatively, you can install `snarkvm` by building from the source code as follows:

```bash
# Download the source code
git clone https://github.com/AleoHQ/snarkvm && cd snarkvm

# Install snarkVM
$ cargo install --path .
```

Now to use `snarkvm`, in your terminal, run:
```bash
snarkvm
```

## 3. Usage Guide

## Diffs to Resolve

- Remove `snarkvm-storage` by reintroducing a virtualized/in-memory ledger
- Unify `snarkvm-parameters` with `snarkos-parameters` - examples and scripts
