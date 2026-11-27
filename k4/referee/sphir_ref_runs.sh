#!/bin/sh
# Referee runs for Corollary S^phi(round) (k4/oc1max_multi.md §17 at d10b8f20). $1: matching's
# data/n5_5pure_s5o0_two_move_starts.jsonl.gz (= the certifier's 280 oc1_fails); $2: the certifier's n = 4 export.
cd "$(dirname "$0")"
python3 sphir_ref.py jsonl "$1" 0 none 4
python3 sphir_ref.py export "$2" 200000 none 4
python3 sphir_ref.py rand 40000 1 none 4
python3 sphir_ref.py rand 40000 1 noP3 4
python3 sphir_ref.py rand 300000 2 none 4
python3 sphir_prefix_ref.py <round_rsd_5pure_witnesses.json.gz> "$1"   # multi's 146-of-410 claim
