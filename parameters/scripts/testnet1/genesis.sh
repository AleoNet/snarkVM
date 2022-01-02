# This script will run the transaction and block generation programs in the `examples` folder and move the resulting `.genesis` files
# to their respective folders under the `src` directory.
# If the transaction size or checksum has changed, you will need to manually update these in each corresponding struct.

# Generate transactions

# Inputs: network, recipient address, amount, genesis filepath, transaction filepath

RUST_BACKTRACE=1 cargo run --example genesis testnet1 aleo1d5hg2z3ma00382pngntdp68e74zv54jdxy249qhaujhks9c72yrs33ddah block.genesis || exit

mv block.genesis ../../src/testnet1/resources || exit
