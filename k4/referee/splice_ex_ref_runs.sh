#!/bin/sh
# Referee runs for Lemma SPLICE (kgen/rounds.md §4.10 at 7ffbfd2e).
cd "$(dirname "$0")"
EXPORT=${1:-../../results/k4_oc1max/two_move_starts_n4.json.gz}
python3 splice_ex_ref.py constructed
python3 splice_ex_ref.py export "$EXPORT" 0 4
python3 splice_ex_ref.py rand 100000 1 4
python3 splice_ex_ref.py rand 300000 2 4
python3 splice_ex_ref.py rand 300000 3 4
# Replay kgen-rounds' printed exceptions: EXCEPTION lines of results/kgen_rounds/splice_search_random_*.log (7ffbfd2e)
#   for f in 4_7_3000_2 4_8_1500_3 5_8_400_4 5_9_300_5; do git show origin/proof/kgen-rounds:results/kgen_rounds/splice_search_random_$f.log | grep '^EXCEPTION ' | sed 's/^EXCEPTION //'; done > exceptions.jsonl
[ -n "$2" ] && python3 splice_ex_replay.py "$2"
# n = 5: results/k4_oc1max/n5/5_pure_s5o0_summary.jsonl.gz from compute/k4-oc1max-cert
[ -n "$3" ] && python3 splice_n5_ref.py "$3" 4 && python3 splice_n5_gaps_ref.py "$3"
