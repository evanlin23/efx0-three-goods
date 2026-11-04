#!/bin/sh
# Every log of k4/sdc.md (from the repository root). The core samples take a few minutes each on 4 CPUs.
set -e
L=results/k4_sdc
python3 k4/sdc/p1_screen.py 1 3 > $L/p1_screen.log 2>&1
grep '^BAD' $L/p1_screen.log | sort -u | python3 k4/sdc/p1_replay.py /dev/stdin > $L/p1_replay.log
python3 k4/sdc/p1_rand.py 1 3 6 300 k4 > $L/p1_rand.log; python3 k4/sdc/p1_rand.py 2 3 6 300 k3 >> $L/p1_rand.log
(python3 k4/sdc/xcheck.py 1 150 3 6; python3 k4/sdc/xcheck.py 2 60 3 7; python3 k4/sdc/xcheck.py 3 20 4 7) > $L/xcheck.log
python3 k4/sdc/sdc_orders.py plain > $L/sdc_screen_plain.log
python3 k4/sdc/sdc_orders.py r1 > $L/sdc_screen_r1_orders.log
python3 k4/sdc/sdsat_r1.py > $L/sdc_screen_r1_sat.log
python3 k4/sdc/sdc_files.py > $L/sdc_de4_instances.log
python3 k4/sdc/sdc_ht.py > $L/sdc_ht.log
for s in rand hyper advt4x advt3x advt2 big8 big12 k3_7 k3_10; do python3 k4/sdc/sdc_rand.py $s 40 6 1; done > $L/sdc_rand.log
python3 k4/sdc/sdc_cores.py k4_certs_2.json.gz,k4_certs_3.json.gz 2000 1 > $L/sdc_cores_n3.log
python3 k4/sdc/sdc_cores.py k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 200 7 > $L/sdc_cores_n4.log
(for a in "1 300 3 7 5" "2 300 3 7 7" "3 200 4 8 6" "4 200 4 9 9" "5 200 5 10 5" "6 200 4 8 8"; do python3 k4/sdc/sdc_gen.py $a; done) > $L/sdc_general.log
(for a in "1 3000 5 8" "2 3000 6 10" "3 2000 8 13" "4 2000 7 11"; do python3 k4/sdc/k3rot.py $a; done) > $L/k3_lbplus_shape.log
python3 k4/sdc/sdc_rules.py screen r1 > $L/sdc_rules_screen.log
(python3 k4/sdc/k3every.py 1 400 5 8; python3 k4/sdc/k3every.py 2 300 6 10) > $L/k3_every_order.log
(python3 k4/sdc/onemove.py screen r1) > $L/onemove_screen.log
(for a in "1 500 4 k4" "2 500 5 k4" "3 300 7 k4" "4 300 10 k4" "5 500 5 k3" "6 300 8 k3"; do python3 k4/sdc/dtops.py $a; done) > $L/distinct_tops.log
python3 k4/sdc/sdc_suite.py > $L/sdc_suite.log
(for a in "1 4 7 100 k4 3" "2 4 8 100 k4 3" "3 5 9 60 k4 3" "4 5 8 100 k3 3" "5 6 10 60 k3 3"; do python3 k4/sdc/p1_sat_rand.py $a; done) > $L/p1_sat_rand.log
(python3 k4/sdc/k3_leader.py 1 40 5 8; python3 k4/sdc/k3_leader.py 2 30 6 10) > $L/k3_leader.log
(python3 k4/sdc/k3_leader_r.py 1 60 5 8 5; python3 k4/sdc/k3_leader_r.py 2 40 6 10 5; python3 k4/sdc/k3_leader_r.py 3 30 8 13 3) > $L/k3_leader_r.log
(python3 k4/sdc/k3_leader_r2.py 1 150 5 8 4; python3 k4/sdc/k3_leader_r2.py 2 100 6 10 4; python3 k4/sdc/k3_leader_r2.py 3 60 8 13 3) > $L/k3_leader_r2.log
(python3 k4/sdc/k3_leader_iter.py 1 300 5 8; python3 k4/sdc/k3_leader_iter.py 2 150 6 10) > $L/k3_leader_iter.log
(python3 k4/sdc/k3_needer.py 1 300 5 8 5; python3 k4/sdc/k3_needer.py 2 150 6 10 5) > $L/k3_needer.log
python3 k4/sdc/k4_leader.py screen 30 1 > $L/k4_leader_screen.log
(python3 k4/sdc/k3_rerun_stats.py 1 300 5 8; python3 k4/sdc/k3_rerun_stats.py 2 150 6 10) > $L/k3_rerun_stats.log
(python3 k4/sdc/dt_check.py 1 3000 4; python3 k4/sdc/dt_check.py 2 2000 6; python3 k4/sdc/dt_check.py 3 500 10) > $L/dt_check.log
python3 k4/sdc/k4_blocks.py 30 1 > $L/k4_blocks_screen.log
python3 k4/sdc/k4_blocks.py adv hyper 40 1 > $L/k4_blocks_hyper.log
python3 k4/sdc/sdf.py screen > $L/sdf_screen.log
python3 k4/sdc/sdc_deficit.py screen r1 > $L/sdc_deficit_screen.log
(python3 k4/sdc/sdc_cheap.py screen; python3 k4/sdc/sdc_cheap.py suite) > $L/sdc_cheap.log
python3 k4/sdc/sdc_cores.py k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 20 11 > $L/sdc_cores_n5.log
(python3 k4/sdc/sdc_need.py screen; python3 k4/sdc/sdc_need.py suite) > $L/sdc_need.log
(python3 k4/sdc/sdc_fewest.py screen; python3 k4/sdc/sdc_fewest.py screen r1) > $L/sdc_fewest.log
python3 k4/sdc/sdc_swap.py screen 20 1 > $L/sdc_swap.log
(python3 k4/sdc/sdc_multigraph.py 1 300 4; python3 k4/sdc/sdc_multigraph.py 2 200 5; python3 k4/sdc/sdc_multigraph.py 3 60 6) > $L/sdc_multigraph.log
python3 k4/sdc/sdc_descent.py screen 12 1 > $L/sdc_descent.log
python3 k4/sdc/sdc_last.py screen > $L/sdc_last.log
python3 k4/sdc/sdc_ps.py screen > $L/sdc_ps_screen.log
python3 k4/sdc/sdc_ps.py screen r1 > $L/sdc_ps_screen_r1.log
python3 k4/sdc/sdc_ps.py suite > $L/sdc_ps_suite.log
(python3 k4/sdc/sdc_linear.py 1 200 5; python3 k4/sdc/sdc_linear.py 2 100 6) > $L/sdc_linear.log
(python3 k4/sdc/sdc_need_owner.py screen; python3 k4/sdc/sdc_need_owner.py suite) > $L/no_screen_suite.log
(for s in rand hyper advt4x advt3x advt2 big8 k3_7; do python3 k4/sdc/sdc_no.py $s 150 1 | tail -1; done; python3 k4/sdc/sdc_no.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 1 | tail -1; python3 k4/sdc/sdc_no.py gen:3:7:7 1000 2 | tail -1; python3 k4/sdc/sdc_no.py gen:4:8:5 800 3 | tail -1) > $L/no_random.log
python3 k4/sdc/sdc_no.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 30000 2 > $L/no_cores_n4.log
python3 k4/sdc/sdc_no.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 8000 3 > $L/no_cores_n5.log
python3 k4/sdc/no_ties.py screen 6 1 > $L/no_ties.log
python3 k4/sdc/no_files.py > $L/no_files.log
python3 k4/sdc/no_owner.py screen > $L/no_owner.log
python3 k4/sdc/no_climb.py 1 4 300 40 > $L/no_climb_n4.log
python3 k4/sdc/no_climb.py 2 5 250 30 > $L/no_climb_n5.log
(for a in "11 2000 2 6 6" "12 2000 2 8 8" "13 1000 2 10 10" "14 2000 2 7 4"; do python3 k4/sdc/sdc_gen.py $a; done) > $L/sdc_n2_general.log
(python3 k4/sdc/no_fresh.py screen; python3 k4/sdc/no_fresh.py suite) > $L/no_fresh.log
(python3 k4/sdc/no_first.py screen; python3 k4/sdc/no_first.py suite; python3 k4/sdc/no_first.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 1; python3 k4/sdc/no_first.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 2) > $L/no_first.log
(python3 k4/sdc/no_walk.py screen; python3 k4/sdc/no_walk.py suite; python3 k4/sdc/no_walk.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 2) > $L/no_walk.log
python3 k4/sdc/no_k3.py 1 200 5 8 > $L/no_k3_n5.log
python3 k4/sdc/no_k3.py 2 150 6 10 > $L/no_k3_n6.log
python3 k4/sdc/no_k3.py 3 60 8 13 > $L/no_k3_n8.log
python3 k4/sdc/k3_defer.py 1 300 5 8 > $L/k3_defer.log
python3 k4/sdc/k3_disp.py 1 300 5 8 > $L/k3_disp_n5.log
python3 k4/sdc/k3_disp.py 2 150 6 10 > $L/k3_disp_n6.log
(for s in big8 big12 big10; do python3 k4/sdc/sdc_no.py $s 400 7; done) > $L/no_big.log
python3 k4/sdc/no_climb.py 3 6 200 20 > $L/no_climb_n6.log
(python3 k4/sdc/nof.py screen; python3 k4/sdc/nof.py suite; python3 k4/sdc/nof.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 1; python3 k4/sdc/nof.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 2; python3 k4/sdc/nof.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 6000 3; for s in rand hyper advt4x advt3x big8 big12; do python3 k4/sdc/nof.py $s 300 5; done; python3 k4/sdc/nof.py gen:3:7:7 1000 2; python3 k4/sdc/nof.py gen:4:8:5 800 3) | grep -v '^\$' > $L/nof.log
python3 k4/sdc/nof_files.py > $L/nof_files.log
python3 k4/sdc/nof_roles.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 2 > $L/nof_roles.log
python3 k4/sdc/nof_climb.py 1 4 300 40 > $L/nof_climb_n4.log
python3 k4/sdc/nof_climb.py 2 5 250 30 > $L/nof_climb_n5.log
(python3 k4/sdc/a3_k4.py screen; python3 k4/sdc/a3_k4.py screen --r1; python3 k4/sdc/a3_k4.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 5000 4 --r1) > $L/a3_k4_screen.log
(python3 k4/sdc/nof.py screen --r1; python3 k4/sdc/nof.py suite --r1; python3 k4/sdc/nof.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 2 --r1; python3 k4/sdc/nof.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 6000 3 --r1) | grep -v '^\$' > $L/nof_r1.log
(python3 k4/sdc/nof_lemmak.py screen; python3 k4/sdc/nof_lemmak.py suite; python3 k4/sdc/nof_lemmak.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 3000 5) > $L/nof_lemmak.log
(python3 k4/sdc/lemma_n_check.py screen; python3 k4/sdc/lemma_n_check.py screen --r1; python3 k4/sdc/lemma_n_check.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 4000 6) > $L/lemma_n_check.log
(python3 k4/sdc/comp_check.py screen; python3 k4/sdc/comp_check.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 4000 6) > $L/comp_check.log
# §15: the owner-free count, the plain-run failures, NOF-L and LB+'s k*
python3 k4/sdc/blocks4.py screen > $L/blocks4_screen.log; python3 k4/sdc/blocks4.py suite > $L/blocks4_suite.log; python3 k4/sdc/blocks4.py screen none > $L/blocks4_screen_none.log
python3 k4/sdc/blocks4.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 4000 13 > $L/blocks4_n3.log; python3 k4/sdc/blocks4.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 4000 11 > $L/blocks4_n4.log; python3 k4/sdc/blocks4.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 1500 12 > $L/blocks4_n5.log
python3 k4/sdc/blocks4r.py screen > $L/blocks4r_screen.log
python3 k4/sdc/blocks4j.py screen > $L/blocks4j_screen.log; python3 k4/sdc/blocks4j.py suite > $L/blocks4j_suite.log
python3 k4/sdc/blocks4j.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 6000 23 > $L/blocks4j_n3.log; python3 k4/sdc/blocks4j.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 6000 21 > $L/blocks4j_n4.log; python3 k4/sdc/blocks4j.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 3000 22 > $L/blocks4j_n5.log
python3 k4/sdc/blocks4j.py screen none > $L/blocks4j_none_screen.log; python3 k4/sdc/blocks4j.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 6000 21 none > $L/blocks4j_none_n4.log; python3 k4/sdc/blocks4j.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 3000 22 none > $L/blocks4j_none_n5.log
python3 k4/sdc/blocks_hand.py > $L/blocks_hand.log
python3 k4/sdc/nof_bad.py screen > $L/nof_bad_screen.log; python3 k4/sdc/nof_bad.py suite > $L/nof_bad_suite.log
python3 k4/sdc/nof_bad.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 6000 23 > $L/nof_bad_n3.log; python3 k4/sdc/nof_bad.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 6000 21 > $L/nof_bad_n4.log; python3 k4/sdc/nof_bad.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 3000 22 > $L/nof_bad_n5.log
python3 k4/sdc/nof_kstar.py screen > $L/nof_kstar_screen.log; python3 k4/sdc/nof_kstar.py suite > $L/nof_kstar_suite.log
python3 k4/sdc/nof_kstar.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 33 > $L/nof_kstar_n3.log; python3 k4/sdc/nof_kstar.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 31 > $L/nof_kstar_n4.log; python3 k4/sdc/nof_kstar.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 6000 32 > $L/nof_kstar_n5.log
(python3 k4/sdc/nofl.py screen; python3 k4/sdc/nofl.py suite; python3 k4/sdc/nofl.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 33) > $L/nofl.log; python3 k4/sdc/nofl_files.py > $L/nofl_files.log
python3 k4/sdc/nofl.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 40000 41 > $L/nofl_n4.log; python3 k4/sdc/nofl.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 12000 42 > $L/nofl_n5.log
python3 k4/sdc/nofl.py climb 44 3 400 60 > $L/nofl_climb_n3.log; python3 k4/sdc/nofl.py climb 43 4 400 40 > $L/nofl_climb_n4.log
python3 k4/sdc/refute_nofl.py > $L/refute_nofl.log
# §16: NO, NOF, NOF-R1 refuted (T3, Q2); Proposition D4; LB4r with the neediest-first Phase 1
python3 k4/sdc/refute_nofl.py > $L/refute_nofl.log
(python3 k4/sdc/nof_d4.py screen; python3 k4/sdc/nof_d4.py suite; python3 k4/sdc/nof_d4.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 33; python3 k4/sdc/nof_d4.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 31; python3 k4/sdc/nof_d4.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 6000 32) > $L/nof_d4.log
(python3 k4/sdc/nof_d4.py screen --nor1; python3 k4/sdc/nof_d4.py suite --nor1; python3 k4/sdc/nof_d4.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 33 --nor1; python3 k4/sdc/nof_d4.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 31 --nor1; python3 k4/sdc/nof_d4.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 6000 32 --nor1) > $L/nof_d4_nor1.log
for F in "" "--nor1"; do S=$( [ -z "$F" ] && echo "" || echo "_nor1" ); (python3 k4/sdc/nf_lb4r.py screen $F; python3 k4/sdc/nf_lb4r.py attempts $F; python3 k4/sdc/nf_lb4r.py suite $F; python3 k4/sdc/nf_lb4r.py files $F; python3 k4/sdc/nf_lb4r.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 20000 33 2 $F; python3 k4/sdc/nf_lb4r.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 20000 31 2 $F; python3 k4/sdc/nf_lb4r.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 6000 32 2 $F; for s in rand hyper advt4x advt3x big8 big12; do python3 k4/sdc/nf_lb4r.py $s 300 5 1 $F; done) > $L/nf_lb4r$S.log; done
(python3 k4/sdc/nf_lb4r.py climb 61 3 600 60 --nor1; NFQ=3 python3 k4/sdc/nf_lb4r.py climb 71 3 600 80 --nor1; NFQ=3 python3 k4/sdc/nf_lb4r.py climb 72 3 600 80; NFQ=3 python3 k4/sdc/nf_lb4r.py climb 73 4 400 50 --nor1; python3 k4/sdc/nf_lb4r.py climb 62 4 600 60 --nor1; python3 k4/sdc/nf_lb4r.py climb 63 5 400 40 --nor1) > $L/nf_lb4r_climb.log
(python3 k4/sdc/nof_var.py special; python3 k4/sdc/nof_var.py suite; python3 k4/sdc/nof_var.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 6000 81; python3 k4/sdc/nof_var.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 5000 82; python3 k4/sdc/nof_var.py screen) > $L/nof_var.log
(python3 k4/sdc/nof_lemmak.py screen --nor1; python3 k4/sdc/nof_lemmak.py suite --nor1; python3 k4/sdc/nof_lemmak.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 3000 7 --nor1) > $L/nof_lemmak_nor1.log
