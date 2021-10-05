# This script will run the inner SNARK setup and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

RUST_BACKTRACE=1 cargo run --release --example setup inner testnet1 || exit

mv inner.metadata ../../src/testnet1/resources
mv inner.proving* ../../src/testnet1/resources
mv inner.verifying ../../src/testnet1/resources
