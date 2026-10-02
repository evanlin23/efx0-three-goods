#!/bin/sh
# Every run of k4/oneneeder.md section 7, regenerated from the "# command:" line of each log (one process at a time).
# Logs and dumps in results/k4_oneneeder/. The zprime runs read k4/sx.md's hunt dumps: set SX to a checkout of
# branch proof/k4-sx (commit ebe244f), e.g. SX=../efx0-sx.
set -e
R=results/k4_oneneeder
SX=${SX:-../efx0-sx}
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n3.json.gz --dump=results/k4_oneneeder/cat_gap_n3.jsonl.gz --rep=20 > $R/cat_gap_n3.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_1.json.gz --dump=results/k4_oneneeder/cat_gap_n4_1.jsonl.gz --rep=20 > $R/cat_gap_n4_1.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_2_s4000.json.gz --dump=results/k4_oneneeder/cat_gap_n4_2_s4000.jsonl.gz --rep=20 > $R/cat_gap_n4_2_s4000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_3_s4000.json.gz --dump=results/k4_oneneeder/cat_gap_n4_3_s4000.jsonl.gz --rep=20 > $R/cat_gap_n4_3_s4000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_pure_s4000.json.gz --dump=results/k4_oneneeder/cat_gap_n4_pure_s4000.jsonl.gz --rep=20 > $R/cat_gap_n4_pure_s4000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_1_s100.json.gz --dump=results/k4_oneneeder/cat_gap_n5_1_s100.jsonl.gz --rep=20 > $R/cat_gap_n5_1_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_2_s100.json.gz --dump=results/k4_oneneeder/cat_gap_n5_2_s100.jsonl.gz --rep=20 > $R/cat_gap_n5_2_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_3_s100.json.gz --dump=results/k4_oneneeder/cat_gap_n5_3_s100.jsonl.gz --rep=20 > $R/cat_gap_n5_3_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_4_s100.json.gz --dump=results/k4_oneneeder/cat_gap_n5_4_s100.jsonl.gz --rep=20 > $R/cat_gap_n5_4_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_pure_s100.json.gz --dump=results/k4_oneneeder/cat_gap_n5_pure_s100.jsonl.gz --rep=20 > $R/cat_gap_n5_pure_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hard_hunt.json.gz --dump=results/k4_oneneeder/cat_hard_hunt.jsonl.gz --rep=20 > $R/cat_hard_hunt.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n4_2_all.json.gz --dump=results/k4_oneneeder/cat_hunt_n4_2_all.jsonl.gz --rep=20 > $R/cat_hunt_n4_2_all.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n4_3_s400k.json.gz --dump=results/k4_oneneeder/cat_hunt_n4_3_s400k.jsonl.gz --rep=20 > $R/cat_hunt_n4_3_s400k.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n4_pure_s400k.json.gz --dump=results/k4_oneneeder/cat_hunt_n4_pure_s400k.jsonl.gz --rep=20 > $R/cat_hunt_n4_pure_s400k.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n5_3_s2000.json.gz --dump=results/k4_oneneeder/cat_hunt_n5_3_s2000.jsonl.gz --rep=20 > $R/cat_hunt_n5_3_s2000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n5_4_s2000.json.gz --dump=results/k4_oneneeder/cat_hunt_n5_4_s2000.jsonl.gz --rep=20 > $R/cat_hunt_n5_4_s2000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n5_pure_s2000.json.gz --dump=results/k4_oneneeder/cat_hunt_n5_pure_s2000.jsonl.gz --rep=20 > $R/cat_hunt_n5_pure_s2000.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_3.json.gz --dump=results/k4_oneneeder/certs3_all.jsonl.gz --rep=2000 --ckpt=results/k4_oneneeder/certs3_all.ckpt > $R/certs3_all.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_3.json.gz --dump=results/k4_oneneeder/certs3_all_v2.jsonl.gz --rep=500 --ckpt=results/k4_oneneeder/certs3_all_v2.ckpt > $R/certs3_all_v2.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_3.json.gz --sample=20000 --seed=11 --dump=results/k4_oneneeder/certs3_r20000_s11.jsonl.gz --rep=200 > $R/certs3_r20000_s11.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_2.json.gz --sample=5000 --seed=23 --bt=all --dump=results/k4_oneneeder/certs4_n4_2_bt_r5000_s23.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4_n4_2_bt_r5000_s23.ckpt > $R/certs4_n4_2_bt_r5000_s23.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_2.json.gz --sample=5000 --seed=22 --dump=results/k4_oneneeder/certs4_n4_2_r5000_s22.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4_n4_2_r5000_s22.ckpt > $R/certs4_n4_2_r5000_s22.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_3.json.gz --sample=5000 --seed=23 --bt=all --dump=results/k4_oneneeder/certs4_n4_3_bt_r5000_s23.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4_n4_3_bt_r5000_s23.ckpt > $R/certs4_n4_3_bt_r5000_s23.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_3.json.gz --sample=20000 --seed=41 --dump=results/k4_oneneeder/certs4_n4_3_r20000_s41.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4_n4_3_r20000_s41.ckpt > $R/certs4_n4_3_r20000_s41.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_3.json.gz --sample=5000 --seed=22 --dump=results/k4_oneneeder/certs4_n4_3_r5000_s22.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4_n4_3_r5000_s22.ckpt > $R/certs4_n4_3_r5000_s22.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_pure.json.gz --sample=20000 --seed=41 --dump=results/k4_oneneeder/certs4_pure_r20000_s41.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4_pure_r20000_s41.ckpt > $R/certs4_pure_r20000_s41.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_pure.json.gz --sample=5000 --seed=22 --dump=results/k4_oneneeder/certs4_pure_r5000_s22.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4_pure_r5000_s22.ckpt > $R/certs4_pure_r5000_s22.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_pure.json.gz --sample=5000 --seed=21 --bt=all --dump=results/k4_oneneeder/certs4pure_bt_r5000_s21.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/certs4pure_bt_r5000_s21.ckpt > $R/certs4pure_bt_r5000_s21.log 2>&1
python3 k4/oneneeder_check.py catalog results/k4_gap/gap_n3.json.gz --shapes > $R/check_gap_n3.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_5_pure.json.gz --cores=4604:4605 --sample=400000 --seed=52 --rep=1 --dump=results/k4_oneneeder/core4604_r400000_s52.jsonl.gz > $R/core4604_r400000_s52.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_5_pure.json.gz --cores=4604:4605 --target --sample=100000 --seed=53 --rep=1 --dump=results/k4_oneneeder/core4604_target_r100000_s53.jsonl.gz > $R/core4604_target_r100000_s53.log 2>&1
python3 k4/oneneeder_run.py inst results/k4_oneneeder/rc_fail_n5_inst.json --rep=1 > $R/rc_fail_n5.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n3.json.gz --t1 > $R/t1_cat_gap_n3.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_1.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n4_1.jsonl.gz --rep=20 > $R/t1_cat_gap_n4_1.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_2_s4000.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n4_2_s4000.jsonl.gz --rep=20 > $R/t1_cat_gap_n4_2_s4000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_3_s4000.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n4_3_s4000.jsonl.gz --rep=20 > $R/t1_cat_gap_n4_3_s4000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n4_pure_s4000.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n4_pure_s4000.jsonl.gz --rep=20 > $R/t1_cat_gap_n4_pure_s4000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_2_s100.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n5_2_s100.jsonl.gz --rep=20 > $R/t1_cat_gap_n5_2_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_3_s100.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n5_3_s100.jsonl.gz --rep=20 > $R/t1_cat_gap_n5_3_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_4_s100.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n5_4_s100.jsonl.gz --rep=20 > $R/t1_cat_gap_n5_4_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/gap_n5_pure_s100.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_gap_n5_pure_s100.jsonl.gz --rep=20 > $R/t1_cat_gap_n5_pure_s100.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n4_3_s400k.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_hunt_n4_3_s400k.jsonl.gz --rep=20 > $R/t1_cat_hunt_n4_3_s400k.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n4_pure_s400k.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_hunt_n4_pure_s400k.jsonl.gz --rep=20 > $R/t1_cat_hunt_n4_pure_s400k.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n5_3_s2000.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_hunt_n5_3_s2000.jsonl.gz --rep=20 > $R/t1_cat_hunt_n5_3_s2000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n5_4_s2000.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_hunt_n5_4_s2000.jsonl.gz --rep=20 > $R/t1_cat_hunt_n5_4_s2000.log 2>&1
python3 k4/oneneeder_run.py catalog results/k4_gap/hunt_n5_pure_s2000.json.gz --t1 --dump=results/k4_oneneeder/t1_cat_hunt_n5_pure_s2000.jsonl.gz --rep=20 > $R/t1_cat_hunt_n5_pure_s2000.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_1.json.gz --target --sample=3000 --seed=31 --dump=results/k4_oneneeder/target4_n4_1_r3000_s31.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/target4_n4_1_r3000_s31.ckpt > $R/target4_n4_1_r3000_s31.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_2.json.gz --target --sample=3000 --seed=31 --dump=results/k4_oneneeder/target4_n4_2_r3000_s31.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/target4_n4_2_r3000_s31.ckpt > $R/target4_n4_2_r3000_s31.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_n4_3.json.gz --target --sample=3000 --seed=31 --dump=results/k4_oneneeder/target4_n4_3_r3000_s31.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/target4_n4_3_r3000_s31.ckpt > $R/target4_n4_3_r3000_s31.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_4_pure.json.gz --target --sample=3000 --seed=31 --dump=results/k4_oneneeder/target4_pure_r3000_s31.jsonl.gz --rep=1 --ckpt=results/k4_oneneeder/target4_pure_r3000_s31.ckpt > $R/target4_pure_r3000_s31.log 2>&1
python3 k4/oneneeder_zprime.py $SX/results/k4_sx/hunt/n3_all_0.jsonl.gz $SX/results/k4_sx/hunt/n3_all_10.jsonl.gz $SX/results/k4_sx/hunt/n3_all_20.jsonl.gz $SX/results/k4_sx/hunt/n3_all_30.jsonl.gz $SX/results/k4_sx/hunt/n3_all_40.jsonl.gz $SX/results/k4_sx/hunt/n3_all_50.jsonl.gz > $R/zprime_sx_hunt_n3_all.log 2>&1
python3 k4/oneneeder_run.py certs results/k4_certs_3.json.gz --t1 --dump=results/k4_oneneeder/t1_certs3_all.jsonl.gz --rep=1000 --ckpt=results/k4_oneneeder/t1_certs3_all.ckpt 2>&1 | gzip -9 > $R/t1_certs3_all.log.gz
