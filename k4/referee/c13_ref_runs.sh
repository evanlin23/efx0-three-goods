# Lemma C13 (k4/ttc.md §14.8). Inputs (data only): the certifier's n = 5 exports on compute/k4-oc1max-cert
#   git show origin/compute/k4-oc1max-cert:results/k4_oc1max/n5/two_move_starts_n5_partial6.json.gz > two_move_starts_n5_partial6.json.gz
#   git show origin/compute/k4-oc1max-cert:results/k4_oc1max/n5/two_move_starts_n5_sel2.json.gz > two_move_starts_n5_sel2.json.gz
#   git show origin/claude/k4-girth:results/k4_girth_rf_n5_class13.jsonl.gz > class13.jsonl.gz      (girth's list, compared only)
python3 c13_ref.py build two_move_starts_n5_partial6.json.gz two_move_starts_n5_sel2.json.gz > c13_ref_build.log   # writes c13_class13_ref.jsonl.gz
python3 c13_ref.py check c13_class13_ref.jsonl.gz class13.jsonl.gz > c13_ref_check.log
python3 c13_ref.py cex > c13_ref_cex.log
python3 c13_ref.py rand 20000 1 > c13_ref_rand_1.log
python3 c13_ref.py rand 200000 2 > c13_ref_rand_2.log
