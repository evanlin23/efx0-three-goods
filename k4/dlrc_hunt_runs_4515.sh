#!/bin/sh
# compute/k4-rc, after the second DL_RC failure (core 4515, m = 12; results/k4_rc/FAILURES.md section 2): climbs on the
# cores obtained from it by deleting one or two goods (m = 10, 11), and from its failing profiles. Resumable.
set -e
cd "$(dirname "$0")/.."
J=${JOBS:-$(nproc)}
H="python3 k4/dlrc_hunt.py"
$H shrink_cores_4515 instcores results/k4_rc/rc_shrink_cores_4515_inst.json --reps=4 --steps=1000 --bt=0.8 --jobs=$J --seed=71 >> results/k4_rc/hunt_shrink_cores_4515.log 2>&1
$H core4515 instcores results/k4_rc/rc_failures_4515_inst.json --reps=1 --steps=1000 --bt=0.8 --jobs=$J --seed=72 --units=12 >> results/k4_rc/hunt_core4515.log 2>&1
