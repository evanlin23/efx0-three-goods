# Conjecture RKMAX at n = 4 (k4/sdc.md §31 end, claude/kind-lamport-y8fdme at c1b2756b). Input (data only):
#   git show origin/compute/k4-oc1max-cert:results/k4_oc1max/two_move_starts_n4.json.gz > two_move_starts_n4.json.gz
python3 rkmax_ref.py all two_move_starts_n4.json.gz 3 > rkmax_ref_all.log
