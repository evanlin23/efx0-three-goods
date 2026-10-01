#!/bin/sh
# compute/k4-rc, task (d), second batch (after k4/dlrc_hunt_runs.sh): objective w2 (chains with least |W| >= 2 first)
# from the failing profiles and the top-ranked cores, more n = 6 extensions, larger samples. Resumable as the first.
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
T=${TMPDIR:-/tmp}/k4_rc_ckpts; mkdir -p $T
for b in n5b:ckpt_n5b_4 n5c:ckpt_n5c_pure n5c:ckpt_n5c_purebt; do
  [ -s $T/${b#*:}.jsonl ] || git show origin/compute/k4-rt4-${b%%:*}:results/k4_rt4/${b#*:}.jsonl > $T/${b#*:}.jsonl
done
H="python3 k4/dlrc_hunt.py"
F10=results/k4_rc/rt4_fail10_inst.json
$H fail10_w2 fail10 $F10 --reps=8 --steps=4000 --obj=w2 --jobs=$J --seed=21 >> results/k4_rc/hunt_fail10_w2.log 2>&1
$H fail10_w2bt fail10 $F10 --reps=4 --steps=4000 --obj=w2 --bt=0.95 --jobs=$J --seed=22 >> results/k4_rc/hunt_fail10_w2bt.log 2>&1
$H extend6_b extend $F10 --exts=400 --steps=600 --obj=w2 --jobs=$J --seed=23 >> results/k4_rc/hunt_extend6_b.log 2>&1
$H ranked_pure_w2 ranked results/k4_certs_5_pure.json.gz $T/ckpt_n5c_pure.jsonl $T/ckpt_n5c_purebt.jsonl results/k4_rc/ckpt_c_purebt.jsonl --top=300 --steps=1500 --obj=w2 --bt=0.9 --jobs=$J --seed=24 >> results/k4_rc/hunt_ranked_pure_w2.log 2>&1
$H ranked_n4_4_w2 ranked results/k4_certs_5_n4_4.json.gz $T/ckpt_n5b_4.jsonl results/k4_rc/ckpt_c_n4_4.jsonl --top=300 --steps=1500 --obj=w2 --bt=0.9 --jobs=$J --seed=25 >> results/k4_rc/hunt_ranked_n4_4_w2.log 2>&1
for f in n4_3 n4_4 pure; do
  $H certs_${f}_b certs results/k4_certs_5_$f.json.gz --min4=3 --sample=1500 --steps=400 --bt=0.8 --jobs=$J --seed=26 >> results/k4_rc/hunt_certs_${f}_b.log 2>&1
done
$H n6_b certs results/k4_certs_6_n4_1.json.gz --sample=4000 --steps=300 --obj=w2 --jobs=$J --seed=27 >> results/k4_rc/hunt_n6_b.log 2>&1
