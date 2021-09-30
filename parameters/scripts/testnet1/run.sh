# These are dependent on each other.
./noop_program.sh || exit
./inner_snark.sh || exit
./outer_snark.sh || exit

./posw_snark.sh || exit

./genesis.sh || exit
