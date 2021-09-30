# These are dependent on each other.
./universal_srs.sh || exit
./noop_program.sh || exit
./inner_snark.sh || exit
./outer_snark.sh || exit

./posw_snark.sh || exit

./genesis.sh || exit
