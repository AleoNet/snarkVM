# This script will run the parameter setup programs in the `examples` folder and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

cargo run --release --example encrypted_record_crh
cargo run --release --example inner_circuit_id_crh
cargo run --release --example ledger_merkle_tree
cargo run --release --example local_data_crh
cargo run --release --example local_data_commitment
cargo run --release --example program_vk_crh
cargo run --release --example record_commitment
cargo run --release --example serial_number_nonce_crh

mv encrypted_record_crh.params ../src/global
mv encrypted_record_crh.checksum ../src/global

mv inner_circuit_id_crh.params ../src/global
mv inner_circuit_id_crh.checksum ../src/global

mv ledger_merkle_tree.params ../src/global
mv ledger_merkle_tree.checksum ../src/global

mv local_data_crh.params ../src/global
mv local_data_crh.checksum ../src/global

mv local_data_commitment.params ../src/global
mv local_data_commitment.checksum ../src/global

mv program_vk_crh.params ../src/global
mv program_vk_crh.checksum ../src/global

mv record_commitment.params ../src/global
mv record_commitment.checksum ../src/global

mv serial_number_nonce_crh.params ../src/global
mv serial_number_nonce_crh.checksum ../src/global

./noop_program_snark.sh

./inner_snark.sh

./outer_snark.sh

./posw_snark.sh
