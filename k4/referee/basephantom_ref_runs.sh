#!/bin/sh
# Referee runs for K4.BASE.DEAD.N4 and K4.BASE.P1FREE.N4 (proof/k4-base-phantom at 0e6d9abc). $1: deadends_n4.jsonl.gz;
# $2: the n = 4 export (results/k4_base_phantom/data/two_move_starts_n4.json.gz = the certifier's, sha256 6159e38d...).
cd "$(dirname "$0")"
python3 basephantom_ref.py dead 1000000 1 4 "$1"
python3 basephantom_ref.py safe 1000000 1 4 "$2"
python3 sep_ref.py 2000000 1
python3 sep_ref.py 500000 2 noP1free
