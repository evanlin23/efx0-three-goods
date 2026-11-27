#!/bin/sh
# Referee runs for Theorem S (k4/oc1max_multi.md §10 at b107719). DATA files: K4.MULTI.DATA from proof/k4-oc1max-multi,
# results/k4_oc1max_multi/hard2_starts.jsonl.gz and hard2_starts_n5.jsonl.gz (read as data only).
cd "$(dirname "$0")"
D1=${1:-../../results/k4_oc1max_multi/hard2_starts.jsonl.gz}
D2=${2:-../../results/k4_oc1max_multi/hard2_starts_n5.jsonl.gz}
python3 theorem_s_ref.py data - "$D1" "$D2"
for mut in anychain noSb noSc noSd; do python3 theorem_s_ref.py data $mut "$D1" "$D2"; done
python3 theorem_s_ref.py rand 40000 1
python3 theorem_s_ref.py rand 40000 2
for mut in anychain noSb noSc noSd; do python3 theorem_s_ref.py rand 10000 3 $mut; done
