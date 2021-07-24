# This script will run the transaction and block generation programs in the `examples` folder and move the resulting `.genesis` files
# to their respective folders under the `src` directory.
# If the transaction size or checksum has changed, you will need to manually update these in each corresponding struct.

# Generate transactions

# Inputs: recipient address, amount, genesis filepath, transaction filepath

cargo run --release --example genesis aleo1ag4alvc4g7d4apzgvr5f4jt44l0aezev2dx8m0klgwypnh9u5uxs42rclr 100 header.genesis transaction.genesis || exit

mv transaction.genesis ../../src/testnet1/genesis || exit

mv header.genesis ../../src/testnet1/genesis || exit
