# Conjecture RKMAX at n = 4 (k4/sdc.md §31 end, claude/kind-lamport-y8fdme at c1b2756b). Input (data only):
#   git show origin/compute/k4-oc1max-cert:results/k4_oc1max/two_move_starts_n4.json.gz > two_move_starts_n4.json.gz
python3 rkmax_ref.py all two_move_starts_n4.json.gz 3 > rkmax_ref_all.log
# n = 5 (sigma optima only): the certifier's n = 5 exports on compute/k4-oc1max-cert, results/k4_oc1max/n5/
python3 rkmax_ref.py sigma two_move_starts_n5_sel2.json.gz 4 > rkmax_ref_n5_sel2.log            # complete lists of 5_pure #419, #447, #38
python3 rkmax_ref.py sigma two_move_starts_n5_sel2.json.gz 3 200 3 > rkmax_ref_n5_sel2_s200.log
python3 rkmax_ref.py sigma two_move_starts_n5_partial6.json.gz 3 200 3 > rkmax_ref_n5_partial6_s200.log   # partial lists, 1 in 200
