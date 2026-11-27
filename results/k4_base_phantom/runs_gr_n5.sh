#!/bin/sh
# GR (gr.py) with the lemma census on every data set, and on the certifier's full n = 5 exports (1,285,930 starts).
D=results/k4_base_phantom/data
O=results/k4_base_phantom
python3 k4/base_phantom/gr.py onemove_multi $D/onemove_hard_multi.jsonl.gz > $O/gr_onemove_multi.log
python3 k4/base_phantom/gr.py onemove_hall $D/onemove_hard_hall2071.jsonl.gz > $O/gr_onemove_hall.log
python3 k4/base_phantom/gr.py onemove_pw $D/onemove_hard_pw291.jsonl.gz > $O/gr_onemove_pw.log
python3 k4/base_phantom/gr.py 5pure $D/n5_5pure_s5o0_two_move_starts.jsonl.gz > $O/gr_5pure.log
MODE=GRR python3 k4/base_phantom/gr.py 5pure_GRR $D/n5_5pure_s5o0_two_move_starts.jsonl.gz > $O/gr_5pure_GRR.log
python3 k4/base_phantom/gr.py walk $D/multi_oc1_fail_walk.jsonl.gz > $O/gr_walk.log
python3 k4/base_phantom/gr.py n4 $D/two_move_starts_n4.json.gz > $O/gr_n4.log
python3 k4/base_phantom/gr.py n5sel2 $D/two_move_starts_n5_sel2.json.gz > $O/gr_n5sel2.log
python3 k4/base_phantom/gr.py n5partial6 $D/two_move_starts_n5_partial6.json.gz > $O/gr_n5partial6.log
