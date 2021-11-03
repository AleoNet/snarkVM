# This script will run the transaction and block generation programs in the `examples` folder and move the resulting `.genesis` files
# to their respective folders under the `src` directory.
# If the transaction size or checksum has changed, you will need to manually update these in each corresponding struct.

# Generate transactions

# Inputs: network, recipient address, amount, genesis filepath, transaction filepath

cargo run --release --example genesis testnet2 aleo1h47qwdqqv25gwp0fkxgnqvm7ykrz0ud2vaw2cj4ac68w8wq5vqqqegh7fp previous_hash.genesis block_header.genesis transaction_1.genesis -- --nocapture || exit

mv previous_hash.genesis ../../src/testnet2/genesis || exit

mv transaction_1.genesis ../../src/testnet2/genesis || exit

mv block_header.genesis ../../src/testnet2/genesis || exit
