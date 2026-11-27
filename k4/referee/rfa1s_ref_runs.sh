# Lemma RF-A1* and Lemma NA (k4/k3_oc1.md §13.5). Inputs (data only): the certifier's n = 5 exports, as in c13_ref_runs.sh
python3 rfa1s_ref.py n5 two_move_starts_n5_partial6.json.gz two_move_starts_n5_sel2.json.gz > rfa1s_ref_n5.log
python3 rfa1s_ref.py gen 400000 2 4 > rfa1s_ref_gen_k4.log
python3 rfa1s_ref.py gen 400000 3 5 > rfa1s_ref_gen_k5.log
python3 rfa1s_ref.py rand 300000 2 4 > rfa1s_ref_rand_k4.log
