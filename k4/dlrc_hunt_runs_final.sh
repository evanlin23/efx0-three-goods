#!/bin/sh
# compute/k4-rc, task (d): the hunt runs for the rest of the time budget, in priority order (they replace what had not run
# yet of k4/dlrc_hunt_runs.sh, _runs2.sh, _runs3.sh, _runs_n4.sh and _runs_shrink.sh; runs already started resume from
# their checkpoints with the same options). Resumable: re-run this script.
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
T=${TMPDIR:-/tmp}/k4_rc_ckpts; mkdir -p $T
for b in n5c:ckpt_n5c_pure n5c:ckpt_n5c_purebt; do
  [ -s $T/${b#*:}.jsonl ] || git show origin/compute/k4-rt4-${b%%:*}:results/k4_rt4/${b#*:}.jsonl > $T/${b#*:}.jsonl
done
H="python3 k4/dlrc_hunt.py"
F10=results/k4_rc/rt4_fail10_inst.json
# resume (same options as when started)
$H ranked_pure ranked results/k4_certs_5_pure.json.gz $T/ckpt_n5c_pure.jsonl $T/ckpt_n5c_purebt.jsonl results/k4_rc/ckpt_c_purebt.jsonl --top=200 --steps=800 --jobs=$J --seed=4 >> results/k4_rc/hunt_ranked_pure.log 2>&1
$H shrink_cores instcores results/k4_rc/rc_shrink_cores_inst.json --reps=6 --steps=1500 --bt=0.6 --jobs=$J --seed=51 >> results/k4_rc/hunt_shrink_cores.log 2>&1
$H n4_pure_k3 certs results/k4_certs_4_pure.json.gz --steps=600 --obj=k3 --bt=0.9 --jobs=$J --seed=43 >> results/k4_rc/hunt_n4_pure_k3.log 2>&1
# the brief's n = 6 seeds and gluings, objective w2
$H n6 certs results/k4_certs_6_n4_1.json.gz --sample=600 --steps=300 --obj=w2 --jobs=$J --seed=6 >> results/k4_rc/hunt_n6.log 2>&1
$H glue glue $F10 --pairs=20 --steps=40 --batch=8 --obj=w2 --init=0 --jobs=$J --seed=7 >> results/k4_rc/hunt_glue.log 2>&1
# n = 6 extensions of the failing n = 5 profiles (an addition), objective w2
$H extend6 extend $F10 --exts=80 --steps=400 --obj=w2 --jobs=$J --seed=5 >> results/k4_rc/hunt_extend6.log 2>&1
# random n = 5 cores with >= 3 four-good agents
for f in pure n4_4 n4_3; do
  $H certs_$f certs results/k4_certs_5_$f.json.gz --min4=3 --sample=200 --steps=400 --bt=0.8 --jobs=$J --seed=8 >> results/k4_rc/hunt_certs_$f.log 2>&1
done
$H core4604 instcores results/k4_rc/rc_failures_n5_inst.json --reps=1 --steps=1500 --bt=0.5 --jobs=$J --seed=52 --units=12 >> results/k4_rc/hunt_core4604.log 2>&1
$H n4_n4_3_k3 certs results/k4_certs_4_n4_3.json.gz --steps=600 --obj=k3 --bt=0.9 --jobs=$J --seed=44 >> results/k4_rc/hunt_n4_n4_3_k3.log 2>&1
$H fail10_w2 fail10 $F10 --reps=2 --steps=2000 --obj=w2 --jobs=$J --seed=21 >> results/k4_rc/hunt_fail10_w2.log 2>&1
