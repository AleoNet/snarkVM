# This script will run the parameter setup programs in the `examples` folder and move the resulting `.params`
# and `.checksum` files to `params` folder under the `src` directory.
# If the parameter size has changed, you will need to manually update these in each corresponding struct.

./noop_program_snark.sh

./inner_snark.sh

./outer_snark.sh

./posw_snark.sh
