# Running with LibAFL

RUSTFLAGS="-Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-trace-pc-guard -Cllvm-args=-sanitizer-coverage-level=1" cargo +nightly run --target x86_64-unknown-linux-gnu -p snarkvm-fuzz -- fuzz --cores 0-14 --input afl/seeds --timeout 1000000`

Run single inputs:

`RUSTFLAGS="-Cpasses=sancov-module -Cllvm-args=-sanitizer-coverage-trace-pc-guard -Cllvm-args=-sanitizer-coverage-level=1" cargo +nightly run --target x86_64-unknown-linux-gnu -p snarkvm-fuzz --release -- execute out/fe44bafddae78ea0`

# Running with libfuzzer 

`cargo fuzz run program`

Run single inputs:

`cargo fuzz run program fuzz/artifacts/program/slow-unit-241cbd6dfb6e53c43c73b62f9384359091dcbf56`
