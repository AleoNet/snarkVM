# This script will run the transaction and block generation programs in the `examples` folder and move the resulting `.genesis` files
# to their respective folders under the `src` directory.
# If the transaction size or checksum has changed, you will need to manually update these in each corresponding struct.

# Generate transactions

# Inputs: network, recipient private key, genesis filepath, transaction filepath

cargo run --release --example genesis testnet3 $1 block.genesis -- --nocapture || exit

mv block.genesis ../../src/testnet3/resources || exit
