#!/bin/sh
# compute/k4-rc, task (d): the adversarial hunt for DL_RC (k4/dlrc_hunt.py). Resumable: re-run this script (each run has
# its own checkpoint and dump under results/k4_rc/; a finished run is skipped unit by unit). The ranked runs read the
# checkpoints of compute/k4-rt4-n5b / -n5c (dlrt4.c runs) from git and this branch's dlrc.c checkpoints.
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
T=${TMPDIR:-/tmp}/k4_rc_ckpts; mkdir -p $T
for b in n5b:ckpt_n5b_3 n5b:ckpt_n5b_3bt n5b:ckpt_n5b_4 n5c:ckpt_n5c_pure n5c:ckpt_n5c_purebt; do
  [ -s $T/${b#*:}.jsonl ] || git show origin/compute/k4-rt4-${b%%:*}:results/k4_rt4/${b#*:}.jsonl > $T/${b#*:}.jsonl
done
H="python3 k4/dlrc_hunt.py"
F10=results/k4_rc/rt4_fail10_inst.json
# 1. from the 10 failing profiles
$H fail10 fail10 $F10 --reps=8 --steps=3000 --batch=24 --jobs=$J --seed=1 >> results/k4_rc/hunt_fail10.log 2>&1
# 2. the cores with >= 3 four-good agents ranked highest by the earlier runs
$H ranked_n4_3 ranked results/k4_certs_5_n4_3.json.gz $T/ckpt_n5b_3.jsonl $T/ckpt_n5b_3bt.jsonl --top=200 --steps=800 --jobs=$J --seed=2 >> results/k4_rc/hunt_ranked_n4_3.log 2>&1
$H ranked_n4_4 ranked results/k4_certs_5_n4_4.json.gz $T/ckpt_n5b_4.jsonl results/k4_rc/ckpt_c_n4_4.jsonl --top=200 --steps=800 --jobs=$J --seed=3 >> results/k4_rc/hunt_ranked_n4_4.log 2>&1
$H ranked_pure ranked results/k4_certs_5_pure.json.gz $T/ckpt_n5c_pure.jsonl $T/ckpt_n5c_purebt.jsonl results/k4_rc/ckpt_c_purebt.jsonl --top=200 --steps=800 --jobs=$J --seed=4 >> results/k4_rc/hunt_ranked_pure.log 2>&1
# 3. n = 6: one agent added to a failing n = 5 profile (an addition to the brief's seeds), objective w2
$H extend6 extend $F10 --exts=150 --steps=400 --obj=w2 --jobs=$J --seed=5 >> results/k4_rc/hunt_extend6.log 2>&1
# 4. n = 6: the cores of k4_certs_6_n4_1, objective w2
$H n6 certs results/k4_certs_6_n4_1.json.gz --sample=2000 --steps=300 --obj=w2 --jobs=$J --seed=6 >> results/k4_rc/hunt_n6.log 2>&1
# 5. gluings of two failing n = 5 profiles sharing a good (n = 10), objective w2
$H glue glue $F10 --pairs=30 --steps=40 --batch=8 --obj=w2 --init=0 --jobs=$J --seed=7 >> results/k4_rc/hunt_glue.log 2>&1
# 6. random cores with >= 3 four-good agents (n = 5)
for f in n4_3 n4_4 pure; do
  $H certs_$f certs results/k4_certs_5_$f.json.gz --min4=3 --sample=400 --steps=400 --jobs=$J --seed=8 >> results/k4_rc/hunt_certs_$f.log 2>&1
done
