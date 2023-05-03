<p align="center">
    <img alt="snarkVM" width="1412" src="https://cdn.aleo.org/snarkvm/banner.png">
</p>

<p align="center">
    <a href="https://circleci.com/gh/AleoHQ/snarkVM"><img src="https://circleci.com/gh/AleoHQ/snarkVM.svg?style=svg&circle-token=6e9ad6d39d95350544f352d34e0e5c62ef54db26"></a>
    <a href="https://codecov.io/gh/AleoHQ/snarkVM"><img src="https://codecov.io/gh/AleoHQ/snarkVM/branch/master/graph/badge.svg?token=cck8tS9HpO"/></a>
    <a href="https://aleo.org/discord"><img src="https://img.shields.io/discord/700454073459015690?logo=discord"/></a>
</p>

## Зміст

* [1. Огляд](#1-огляд)
* [2. Посібник зі збірки](#2-посібник-зі-збірки)
* [3. Посібник з використання](#3-посібник-з-використання)
* [4. Ліцензія](#4-ліцензія)

## 1. Огляд

|       Package       | Crate.io                                                                         |        `std`       |       `wasm`       |
|:-------------------:|----------------------------------------------------------------------------------|:------------------:|:------------------:|
|       snarkvm       | ![crates.io](https://img.shields.io/crates/v/snarkvm.svg?color=neon)             | :white_check_mark: | :white_check_mark: |
| snarkvm-algorithms  | ![crates.io](https://img.shields.io/crates/v/snarkvm-algorithms.svg?color=neon)  | :white_check_mark: | :white_check_mark: |
|   snarkvm-circuit   | ![crates.io](https://img.shields.io/crates/v/snarkvm-circuit.svg?color=neon)     | :white_check_mark: | :white_check_mark: |
|   snarkvm-console   | ![crates.io](https://img.shields.io/crates/v/snarkvm-console.svg?color=neon)     | :white_check_mark: | :white_check_mark: |
|   snarkvm-curves    | ![crates.io](https://img.shields.io/crates/v/snarkvm-curves.svg?color=neon)      | :white_check_mark: | :white_check_mark: |
|   snarkvm-fields    | ![crates.io](https://img.shields.io/crates/v/snarkvm-fields.svg?color=neon)      | :white_check_mark: | :white_check_mark: |
| snarkvm-parameters  | ![crates.io](https://img.shields.io/crates/v/snarkvm-parameters.svg?color=neon)  | :white_check_mark: | :white_check_mark: |
|    snarkvm-r1cs     | ![crates.io](https://img.shields.io/crates/v/snarkvm-r1cs.svg?color=neon)        | :white_check_mark: | :white_check_mark: |
| snarkvm-synthesizer | ![crates.io](https://img.shields.io/crates/v/snarkvm-synthesizer.svg?color=neon) | :white_check_mark: | :white_check_mark: |
|  snarkvm-utilities  | ![crates.io](https://img.shields.io/crates/v/snarkvm-utilities.svg?color=neon)   | :white_check_mark: | :white_check_mark: |
|    snarkvm-wasm     | ![crates.io](https://img.shields.io/crates/v/snarkvm-wasm.svg?color=neon)        | :white_check_mark: | :white_check_mark: |

Для отримання додаткової інформації відвідайте [Ласкаво просимо до Aleo](https://github.com/AleoHQ/welcome) для початку роботи.

## 2. Посібник зі збірки

### 2.1 Встановлення Rust

Ми рекомендуємо встановлювати Rust за допомогою [rustup](https://www.rustup.rs/). Ви можете встановити `rustup` таким чином:

- macOS або Linux:
  ```bash
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
  ```

- Windows (64-bit):  
  
  Завантажте [виконавчий файл Windows 64-bit](https://win.rustup.rs/x86_64) або
  [виконавчий файл Windows 32-bit](https://win.rustup.rs/i686) та дотримуйтесь вказівок на екрані.

### 2.2a Збірка з Crates.io

Ми рекомендуємо встановлювати `snarkvm` таким чином. У вашому терміналі виконайте:

```bash
cargo install snarkvm
```

Тепер, щоб використовувати `snarkvm`, у вашому терміналі виконайте:

```bash
snarkvm
```
 
### 2.2b Збірка з початкового коду


В якості альтернативи, ви можете встановити `snarkvm`, зібравши його з початкового коду, як описано нижче:

```bash
# Завантажте початковий код
git clone https://github.com/AleoHQ/snarkvm && cd snarkvm

# Встановіть snarkVM
$ cargo install --path .
```

Тепер, щоб використовувати `snarkvm`, у вашому терміналі виконайте:
```bash
snarkvm
```

## 3. Посібник з використання

## 4. Ліцензія

[![Ліцензія: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](./LICENSE.md)
