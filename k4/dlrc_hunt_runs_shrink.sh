#!/bin/sh
# compute/k4-rc, after the DL_RC failure at n = 5, m = 13 (results/k4_rc/FAILURES.md): climbs on the cores obtained from
# the failing core by deleting one or two goods (results/k4_rc/rc_shrink_cores_inst.json, m = 11, 12), starting at the
# failing values' order types where they stay valid, and on the failing core itself (more failing profiles).
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
H="python3 k4/dlrc_hunt.py"
$H shrink_cores instcores results/k4_rc/rc_shrink_cores_inst.json --reps=6 --steps=1500 --bt=0.6 --jobs=$J --seed=51 >> results/k4_rc/hunt_shrink_cores.log 2>&1
$H core4604 instcores results/k4_rc/rc_failures_n5_inst.json --reps=1 --steps=1500 --bt=0.5 --jobs=$J --seed=52 --units=12 >> results/k4_rc/hunt_core4604.log 2>&1
