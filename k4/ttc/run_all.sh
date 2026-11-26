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
