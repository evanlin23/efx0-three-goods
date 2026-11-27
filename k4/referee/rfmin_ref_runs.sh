# twins' k4/RFMIN.md (PR #156). Inputs (data only): the certifier's exports, as in rkmax_ref_runs.sh and c13_ref_runs.sh
python3 rfmin_ref.py data two_move_starts_n4.json.gz two_move_starts_n5_partial6.json.gz two_move_starts_n5_sel2.json.gz > rfmin_ref_data.log
python3 rfmin_ref.py top 100000 2 > rfmin_ref_top.log
python3 rfmin_ref.py abs 200000 3 4 > rfmin_ref_abs_k4.log
python3 rfmin_ref.py abs 100000 4 5 > rfmin_ref_abs_k5.log
# Lemma REC-EXISTS (every OC1-failing maximum-matching start has a receiver): random search
python3 norecv_ref.py 300000 2 3 5 > norecv_ref_n35.log
python3 norecv_ref.py 20000 3 6 6 > norecv_ref_n6.log
