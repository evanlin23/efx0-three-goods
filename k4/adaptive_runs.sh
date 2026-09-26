#!/bin/bash
# Every log of k4/adaptive.md (about 3 hours on 4 CPUs; the n = 4 runs with three 4-good agents dominate).
# k4/adaptive_verify_H.py and attempts/k4_adaptive_attempts.py use k4/c4_verify_H (PR #33, on main);
# k4/adaptive_crosscheck.py needs k4/c4check.c of branch proof/k4-c4one (PR #37) compiled, in C4CHECK_BIN.
cd "$(dirname "$0")/.."
R=results; C2=$R/k4_certs_2.json.gz; C3=$R/k4_certs_3.json.gz; N41=$R/k4_certs_4_n4_1.json.gz
N42=$R/k4_certs_4_n4_2.json.gz; N43=$R/k4_certs_4_n4_3.json.gz; P4=$R/k4_certs_4_pure.json.gz
N5="$R/k4_certs_5_n4_1.json.gz $R/k4_certs_5_n4_2.json.gz $R/k4_certs_5_n4_3.json.gz $R/k4_certs_5_n4_4.json.gz $R/k4_certs_5_pure.json.gz"
# rules on the small classes (§2, §4, §5)
(for o in -A0 -A1 -A2 -A3 -A4 -A5 -A6 -A7 -A8 -A9 -A10 -A11 -A12 -A13 -A14 -A15 -A16 -A24 -i2; do
   python3 k4/adaptive_run.py $C2 $C3 $o -r3 --show=0 --jobs=2; done) > $R/k4_adaptive_rules_n23.log 2>&1
(for o in -A0 -A2 -A3 -A12 -A14 -A15 -A16 -A24 -i2; do python3 k4/adaptive_run.py $N41 $N42 $o -r3 --show=3; done) > $R/k4_adaptive_rules_n4.log 2>&1
python3 k4/adaptive_run.py $N43 -A14 -r3 -K1 -f2 --show=40 > $R/k4_adaptive_A14_n4_3.log 2>&1
python3 k4/adaptive_run.py $N43 -A16 -r3 --show=20 > $R/k4_adaptive_A16_n4_3.log 2>&1
python3 k4/adaptive_run.py $N43 -i2 -r3 --show=20 > $R/k4_adaptive_exists_n4_3.log 2>&1
(python3 k4/adaptive_run.py $P4 -A16 -r3 -S20000 -K2 -f3 --show=20; python3 k4/adaptive_run.py $P4 -A16 -r3 -H5000 -K2 -f3 --show=20) > $R/k4_adaptive_A16_pure4.log 2>&1
python3 k4/adaptive_run.py $N5 -A16 -r3 -S5000 -K2 -f3 --jobs=2 --show=50 > $R/k4_adaptive_A16_n5_sample.log 2>&1
# adversarial sets (§2)
(for f in deep hard4 hard5; do python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz -A16 -r3 -H3000 -K2 -f3 --show=50; done
 for f in grow1 grow2 grow3 rc6_big rc6_n4_2 rc6_n4_4 rc6_n4_6 rc6_rand rc7 rc8; do
   python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz -A16 -r3 -H2000 -K2 -f3 --show=50; done) > $R/k4_adaptive_hill.log 2>&1
python3 k4/adaptive_gm4_profiles.py > $R/k4_adaptive_gm4_profiles.log 2>&1   # provenance of the GM4 profile file (checks it)
(for o in -A0 -A16 -A24; do python3 k4/adaptive_run.py --profiles=$R/k4_adaptive_gm4_profiles.jsonl $o -r3; done) > $R/k4_adaptive_hard.log 2>&1
# H_t (§3)
python3 k4/adaptive_H.py 1,2,3,4,5,6,7,8 --perms=5 -A16 -r1 -w0 --timeout=1200 > $R/k4_adaptive_A16_H.log 2>&1
(for o in -A1 -A2; do python3 k4/adaptive_H.py 1,2,3,4,5,6,7,8 --perms=5 $o -r1 -w0 --timeout=600; done) > $R/k4_adaptive_cheap_H.log 2>&1
python3 k4/adaptive_verify_H.py 5 200 > $R/k4_adaptive_verify_H.log 2>&1
python3 k4/adaptive_verify_H.py 3 200 --relabel > $R/k4_adaptive_verify_H_relabel.log 2>&1
# rejected rules (§5): smallest failures, reproduced; mining (§4)
(echo "# the least m at which each rule needs two rotations: every strict profile of every n = 3 core"
 for A in 0 1 2 4 5 6 7 8 9 10 11 13; do python3 k4/adaptive_run.py $C3 -A$A -r1 -f200 --show=100000 --jobs=2 2>/dev/null |
   grep "^FAIL" | awk -v a=$A '{match($0,/m=[0-9]+/); print "rule", a, "m=" substr($0,RSTART+2,RLENGTH-2), $0}' | sort -k3,3 -t= -n | head -1; done) > $R/k4_adaptive_smallest.log 2>&1
python3 attempts/k4_adaptive_attempts.py > $R/k4_adaptive_attempts.log 2>&1
python3 k4/adaptive_mine.py $C3 --per=60 > $R/k4_adaptive_mine_n3.log 2>&1
# rule 2 alone (§5)
(python3 k4/adaptive_run.py $N5 -A2 -r3 -S1000 -K3 -f3 --jobs=1 --show=50
 for f in hard4 hard5 grow1 rc6_big rc7; do python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz -A2 -r3 -H2000 -K3 -f3 --show=50 --jobs=1; done) > $R/k4_adaptive_A2.log 2>&1
# matching-based rules (§5)
python3 k4/adaptive_matching_check.py > $R/k4_adaptive_matching_check.log 2>&1
(for A in -A17 -A18 -A25; do python3 k4/adaptive_run.py $C3 $A -r3 -K2 -f100000 --show=100000 --jobs=2; done) > $R/k4_adaptive_matching_deep_n3.log 2>&1
(python3 k4/adaptive_matching_ties.py; python3 k4/adaptive_matching_ties.py --deep=$R/k4_adaptive_matching_deep_n3.log) > $R/k4_adaptive_matching_ties.log 2>&1
(for A in -A17 -A18 -A25; do
  python3 k4/adaptive_run.py $C2 $C3 $N41 $N42 $N43 $A -r3 -K2 -f1 --show=2
  python3 k4/adaptive_run.py $N5 $A -r3 -S1000 -K3 -f1 --show=2
  python3 k4/adaptive_run.py --profiles=$R/k4_adaptive_gm4_profiles.jsonl $A -r3
  for f in hard4 hard5; do python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz $A -r3 -H2000 -K3 -f1 --show=2; done
 done
 for A in -A17 -A18 -A25; do python3 k4/adaptive_H.py 1,2,3 --perms=5 $A -r3 -w0 --timeout=300; done) > $R/k4_adaptive_matching.log 2>&1
# the multi-4-good gap (§6)
python3 k4/adaptive_crosscheck.py $C2 $C3 $N41 $N42 > $R/k4_adaptive_crosscheck.log 2>&1
python3 k4/adaptive_uncovered.py $C2 $C3 $N41 $N42 > $R/k4_adaptive_uncovered.log 2>&1
( (for f in $C2 $C3 $N41 $N42; do
   python3 k4/adaptive_run.py $f -A22 -C3 -Z1 -r3 --show=3; python3 k4/adaptive_run.py $f -A22 -C2 -Z1 -r3 --show=3
   python3 k4/adaptive_run.py $f -A22 -C3 -Z2 -r3 --show=3; done)
 for k in 1 2 3; do for c in -C2 -C3; do python3 k4/adaptive_run.py $C3 --n4=$k -A22 $c -r3 --show=0 --jobs=2; done; done) > $R/k4_adaptive_cover_N.log 2>&1
(python3 k4/adaptive_run.py $C2 $C3 $N42 -i2 -r0 -w0 --show=0
 python3 k4/adaptive_run.py $C2 $C3 $N42 -i2 -r3 --show=0
 for o in "-r0 -w0" "-r3 -w0" "-r3"; do python3 k4/adaptive_uncovered.py $C2 $C3 $N42 -A26 -C3 $o; done) > $R/k4_adaptive_basewants.log 2>&1
python3 k4/adaptive_lb4check.py $C2 $C3 --jobs=2 > $R/k4_adaptive_lb4check.log 2>&1
