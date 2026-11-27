#!/bin/sh
# Referee runs for matching's ROUND-RSD / Lemma LIFT* (rounds) / K4.MATCH.RSD.BASE (k4/matching.md §6, 56e64a9f).
# Arguments: a directory holding, from proof/k4-matching, results/k4_matching/{round_rsd_*_witnesses.json.gz,
# data/two_move_starts_n4.json.gz (= the certifier's n = 4 export), data/n5_5pure_s5o0_two_move_starts.jsonl.gz,
# n5_walk164.jsonl, n5_walk164_long.jsonl.gz} (flattened), and a directory with data/onemove_hard_{multi,hall2071,pw291}.jsonl.gz.
cd "$(dirname "$0")"; R=$1; B=$2
python3 round_rsd_ref.py wit $R/round_rsd_n4_witnesses.json.gz $R/n4.json.gz 4
python3 round_rsd_ref.py wit $R/round_rsd_5pure_witnesses.json.gz $R/n5_5pure_s5o0_two_move_starts.jsonl.gz 4
python3 round_rsd_ref.py wit $R/round_rsd_n5walk_witnesses.json.gz $R/n5_walk164.jsonl $R/n5_walk164_long.jsonl.gz 4
for mut in none skip; do
  python3 round_rsd_ref.py lift 280 1 $mut 4 $R/n5_5pure_s5o0_two_move_starts.jsonl.gz
  python3 round_rsd_ref.py lift 3000 1 $mut 4 $R/n5_walk164.jsonl $R/n5_walk164_long.jsonl.gz
  python3 round_rsd_ref.py lift 5000 1 $mut 4 $R/n4.json.gz
done
python3 base_ref.py $B/onemove_hard_multi.jsonl.gz $B/onemove_hard_hall2071.jsonl.gz $B/onemove_hard_pw291.jsonl.gz 4
