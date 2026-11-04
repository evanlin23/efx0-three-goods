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
