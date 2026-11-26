#!/bin/sh
# Reproduce every log of k4/ttc.md (run from the repository root).  Times on 4 CPUs: a few minutes each, except the
# climbs and the grid (tens of minutes).
set -e
cd "$(dirname "$0")"
L=../../results/k4_ttc
P=$(python3 -c "print(','.join(h+'/'+i for h in ['val','minval','lean'] for i in ['val','minval','minimal','lean','small']))")
python3 ttc_test.py special > $L/ttc_test_special.log
python3 ttc_test.py screen > $L/ttc_test_screen.log
python3 ttc_test.py suite > $L/ttc_test_suite.log
python3 ttc_test.py special prefs=$P prios=rev,pi,danger,revdanger modes=one,head,rep,rephead baseline=0 > $L/ttc_grid_special.log
python3 ttc_test.py screen prefs=$P prios=rev,pi,danger,revdanger modes=one,head,rep,rephead baseline=0 > $L/ttc_grid_screen.log
Q="minval,minval/small,minval/val,minimal,lean,val"
python3 ttc_test.py core:n3 3000 91 prefs=$Q prios=rev,revdanger,pi modes=one,rep,rephead baseline=0 > $L/ttc_test_n3.log
python3 ttc_test.py core:n4 1500 92 prefs=$Q prios=rev,pi modes=one,rep baseline=0 > $L/ttc_test_n4.log
python3 ttc_test.py logs prefs=$Q prios=rev,pi modes=one,rep baseline=0 > $L/ttc_test_logs.log
(python3 ttc_fail.py special; python3 ttc_fail.py screen) > $L/ttc_fail.log
(python3 ttc_diag.py special show=3; python3 ttc_diag.py core:n3 3000 91 show=2 nmax=3) > $L/ttc_diag.log
(python3 ttc_heads.py special; python3 ttc_heads.py screen) > $L/ttc_heads.log
R5=rules=val,minval,minimal,lean,small
(python3 ttc_union.py special $R5; python3 ttc_union.py screen $R5) > $L/ttc_union.log
(python3 ttc_cover.py special $R5; python3 ttc_cover.py dich $R5; python3 ttc_cover.py screen $R5) > $L/ttc_cover.log
(python3 ttc_cover.py core:n3 3000 91; python3 ttc_cover.py core:n4 1500 92; python3 ttc_cover.py screen) > $L/ttc_cover2.log
(python3 ttc2.py special; python3 ttc2.py dich; python3 ttc2.py screen) > $L/ttc2_curated.log
(python3 ttc2.py suite; python3 ttc2.py logs; python3 ttc2.py core:n3 3000 91; python3 ttc2.py core:n4 1500 92; python3 ttc2.py core:n5 150 93) > $L/ttc2_data.log
python3 ttc2.py big:6-9 400 5 nmax=9 orders=12 > $L/ttc2_bign.log
python3 ttc2_fail_union.py > $L/ttc2_failures_union.log
python3 repro_attempts.py > $L/repro_attempts.log
(python3 min_rule.py special; python3 min_rule.py screen) > $L/min_rule.log
(python3 local_rule.py special; python3 local_rule.py screen) > $L/local_rule.log
(python3 displace.py special; python3 displace.py screen) > $L/displace.log
(python3 displace.py suite; python3 displace.py logs; python3 displace.py core:n3 3000 91; python3 displace.py core:n4 1500 92; python3 displace.py core:n5 150 93) > $L/displace_all.log
(python3 head_owner.py special; python3 head_owner.py dich; python3 head_owner.py screen) > $L/head_owner.log
(python3 head_owner.py suite; python3 head_owner.py logs nmax=5; python3 head_owner.py core:n3 3000 91; python3 head_owner.py core:n4 1500 92; python3 head_owner.py core:n5 150 93) > $L/head_owner_all.log
python3 head_climb.py 61 3 1200 12 > $L/head_climb_n3.log
python3 head_climb.py 62 4 400 8 > $L/head_climb_n4.log
python3 head_climb.py 71 3 3000 25 > $L/head_climb_n3_long.log
python3 head_climb.py 72 4 1200 15 > $L/head_climb_n4_long.log
python3 head_rule.py special > $L/head_rule.log; python3 head_rule.py dich >> $L/head_rule.log; python3 head_rule.py screen >> $L/head_rule.log; python3 head_rule.py core:n3 3000 91 >> $L/head_rule.log
(python3 chain_shape.py special; python3 chain_shape.py dich; python3 chain_shape.py screen; python3 chain_shape.py suite; python3 chain_shape.py core:n3 3000 91; python3 chain_shape.py core:n4 1500 92; python3 chain_shape.py core:n5 150 93; python3 chain_shape.py logs nmax=5) > $L/chain_shape.log
(python3 chain_shape.py k3:5 600 31; python3 head_rule.py k3:5 600 31; python3 chain_shape.py k3:5 3000 32; python3 chain_shape.py k3:6 600 33 nmax=6) > $L/chain_shape_k3.log
(python3 head_bign.py big:6-9 2000 11 orders=12 tlim=120; python3 head_bign.py logs nmin=6 nmax=9 orders=12 tlim=120) > $L/head_bign.log
python3 head_climb.py 81 3 3000 20 hd > $L/head_climb_hd_n3.log
python3 head_climb.py 82 4 1000 12 hd > $L/head_climb_hd_n4.log
python3 head_climb.py 83 5 150 4 hd > $L/head_climb_hd_n5.log
python3 head_bign_climb.py 12 400 10 21 6 8 > $L/head_bign_climb_6_8.log      # stopped by hand after 7 runs (see the log)
python3 head_bign_climb.py 12 400 10 31 6 8 ends > $L/head_bign_climb_ends_6_8.log
python3 hd_fail_check.py > $L/hd_fail_check.log
(python3 refute_head.py 0; python3 refute_head.py 1) > $L/refute_head.log
python3 pointer.py special > $L/pointer.log; for a in dich screen suite 'core:n3 3000 91' 'core:n4 1500 92' 'core:n5 150 93' 'logs nmax=5' 'k3:5 3000 32'; do python3 pointer.py $a >> $L/pointer.log; done
python3 head_bign_climb.py 6 300 10 41 6 6 ends seeded > $L/head_bign_climb_ends_seeded.log
python3 oc1_false_check.py > $L/oc1_false_check.log
(python3 refute_oc1.py; for i in 0 10 20 40 60 83; do python3 refute_oc1.py ../../results/k4_ttc/oc1_counterexamples.json $i | grep -E '^order|^1\.|^2\.|moves after|OC1 FAILS'; done) > $L/refute_oc1.log
(python3 k4/sdc/oc_absorb.py cores:k4_certs_5_n4_3.json.gz 200 94; python3 k4/sdc/oc_absorb.py cores:k4_certs_5_n4_4.json.gz 200 95; python3 k4/sdc/oc_absorb.py cores:k4_certs_5_pure.json.gz 200 96) > $L/oc1_n5_many4.log   # run from the repository root
python3 oc1_core_profiles.py 2000 7 > $L/oc1_core_profiles.log   # plus the OC check appended by hand (see the log)
python3 core_climb.py 48 400 10 71 6 7 > $L/core_climb_6_7.log
python3 core_climb.py 12 400 24 81 5 5 free seeded > $L/core_climb_oc_seeded.log
python3 core_climb.py 6 400 30 91 5 5 seeded seed=oc1_mc2_candidate.json mc2 > $L/core_climb_mc2_seeded.log
python3 core_climb.py 36 400 12 92 6 8 mc2 > $L/core_climb_mc2_6_8.log
