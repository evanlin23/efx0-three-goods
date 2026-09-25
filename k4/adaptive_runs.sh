#!/bin/bash
# Every log of k4/adaptive.md. Hours on 4 CPUs (pure n = 4 and the n = 4 every-order runs dominate).
# adaptive_verify_H.py and attempts/k4_adaptive_attempts.py need PR #33's k4/c4_verify_H (C4VERIFY_DIR);
# adaptive_crosscheck.py needs k4/c4check.c of proof/k4-c4one compiled (C4CHECK_BIN).
cd "$(dirname "$0")/.."
R=results
C2=$R/k4_certs_2.json.gz; C3=$R/k4_certs_3.json.gz
(for o in -A0 -A1 -A2 -A3 -A4 -A5 -A6 -A7 -A8 -A9 -A10 -A11 -A12 -A13 -A14 -A15 -A16 -A24 -i2; do
   python3 k4/adaptive_run.py $C2 $C3 $o -r3 --show=0; done) > $R/k4_adaptive_rules_n23.log 2>&1
(for o in -A0 -A2 -A3 -A12 -A14 -A15 -A16 -A24 -i2; do
   python3 k4/adaptive_run.py $R/k4_certs_4_n4_1.json.gz $R/k4_certs_4_n4_2.json.gz $o -r3 --show=3; done) > $R/k4_adaptive_rules_n4.log 2>&1
python3 k4/adaptive_run.py $R/k4_certs_4_n4_3.json.gz -A14 -r3 -K1 -f2 --show=40 > $R/k4_adaptive_A14_n4_3.log 2>&1
python3 k4/adaptive_run.py $R/k4_certs_4_n4_3.json.gz -A16 -r3 --show=20 > $R/k4_adaptive_A16_n4_3.log 2>&1
python3 k4/adaptive_run.py $R/k4_certs_4_n4_3.json.gz -i2 -r3 --show=20 > $R/k4_adaptive_exists_n4_3.log 2>&1
python3 k4/adaptive_run.py $R/k4_certs_4_n4_3.json.gz -A24 -r3 -K2 -f2 --show=10 --jobs=1 > $R/k4_adaptive_A24_n4_3.log 2>&1
python3 k4/adaptive_run.py $R/k4_certs_4_pure.json.gz -A16 -r3 --show=20 > $R/k4_adaptive_A16_pure4.log 2>&1
python3 k4/adaptive_run.py $R/k4_certs_5_n4_1.json.gz $R/k4_certs_5_n4_2.json.gz $R/k4_certs_5_n4_3.json.gz \
  $R/k4_certs_5_n4_4.json.gz $R/k4_certs_5_pure.json.gz -A16 -r3 -S5000 -K2 -f3 --jobs=2 --show=50 > $R/k4_adaptive_A16_n5_sample.log 2>&1
(for f in deep hard4 hard5; do python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz -A16 -r3 -H3000 -K2 -f3 --show=50; done
 for f in grow1 grow2 grow3 rc6_big rc6_n4_2 rc6_n4_4 rc6_n4_6 rc6_rand rc7 rc8; do
   python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz -A16 -r3 -H2000 -K2 -f3 --show=50; done) > $R/k4_adaptive_hill.log 2>&1
(for o in -A0 -A16 -A24; do python3 k4/adaptive_run.py --profiles=$R/k4_adaptive_gm4_profiles.jsonl $o -r3; done) > $R/k4_adaptive_hard.log 2>&1
python3 k4/adaptive_H.py 1,2,3,4,5,6,7,8 --perms=5 -A16 -r1 -w0 --timeout=1200 > $R/k4_adaptive_A16_H.log 2>&1
python3 k4/adaptive_verify_H.py 5 200 > $R/k4_adaptive_verify_H.log 2>&1
python3 k4/adaptive_mine.py $C3 --per=60 > $R/k4_adaptive_mine_n3.log 2>&1
python3 k4/adaptive_uncovered.py $C2 $C3 $R/k4_certs_4_n4_1.json.gz $R/k4_certs_4_n4_2.json.gz > $R/k4_adaptive_uncovered.log 2>&1
python3 k4/adaptive_crosscheck.py $C2 $C3 $R/k4_certs_4_n4_1.json.gz $R/k4_certs_4_n4_2.json.gz > $R/k4_adaptive_crosscheck.log 2>&1
python3 attempts/k4_adaptive_attempts.py > $R/k4_adaptive_attempts.log 2>&1
python3 k4/adaptive_H.py 1,2,3,4,5,6,7,8 --perms=5 -A1 -r1 -w0 --timeout=600 > $R/k4_adaptive_cheap_H.log 2>&1; python3 k4/adaptive_H.py 1,2,3,4,5,6,7,8 --perms=5 -A2 -r1 -w0 --timeout=600 >> $R/k4_adaptive_cheap_H.log 2>&1
(for f in $C2 $C3 $R/k4_certs_4_n4_1.json.gz $R/k4_certs_4_n4_2.json.gz; do
   python3 k4/adaptive_run.py $f -A22 -C3 -Z1 -r3 --show=3; python3 k4/adaptive_run.py $f -A22 -C2 -Z1 -r3 --show=3; done) > $R/k4_adaptive_cover_N.log 2>&1
python3 k4/adaptive_run.py $R/k4_certs_5_n4_1.json.gz $R/k4_certs_5_n4_2.json.gz $R/k4_certs_5_n4_3.json.gz $R/k4_certs_5_n4_4.json.gz $R/k4_certs_5_pure.json.gz -A2 -r3 -S1000 -K3 -f3 --show=50 > $R/k4_adaptive_A2.log 2>&1; for f in hard4 hard5 grow1 rc6_big rc7; do python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz -A2 -r3 -H2000 -K3 -f3 --show=50; done >> $R/k4_adaptive_A2.log 2>&1
python3 k4/adaptive_H.py 8 -A16 -r1 -w0 --timeout=10800 > $R/k4_adaptive_A16_H8.log 2>&1
R=results
for A in -A17 -A18 -A25; do
  python3 k4/adaptive_run.py $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz $R/k4_certs_4_n4_1.json.gz $R/k4_certs_4_n4_2.json.gz $R/k4_certs_4_n4_3.json.gz $A -r3 -K2 -f1 --show=3 --jobs=2
  python3 k4/adaptive_run.py $R/k4_certs_5_n4_1.json.gz $R/k4_certs_5_n4_2.json.gz $R/k4_certs_5_n4_3.json.gz $R/k4_certs_5_n4_4.json.gz $R/k4_certs_5_pure.json.gz $A -r3 -S1000 -K3 -f1 --show=3 --jobs=2
  python3 k4/adaptive_run.py --profiles=$R/k4_adaptive_gm4_profiles.jsonl $A -r3 --jobs=2
  for f in hard4 hard5 grow1 rc6_big rc7; do python3 k4/adaptive_run.py $R/k4_lb4r_cores_$f.json.gz $A -r3 -H2000 -K3 -f1 --show=3 --jobs=2; done
done
for A in -A17 -A25; do python3 k4/adaptive_H.py 1,2,3,4,5,6,7 --perms=5 $A -r3 -w0 --timeout=900; done
# (the block above writes results/k4_adaptive_matching.log)
