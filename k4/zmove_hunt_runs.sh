#!/bin/sh
# Phase 3 hunts of workstream compute/k4-zmove (k4/zmove_hunt.py), one process and one checkpoint (OUT.state.json) each;
# rerunning a name resumes it. Usage: sh k4/zmove_hunt_runs.sh NAME MINUTES RNG SEEDFILE[:i] [extra options]
H=results/k4_zmove/hunt
mkdir -p $H
n=$1; mi=$2; r=$3; sf=$4; shift 4
nice -n 10 python3 k4/zmove_hunt.py $H/$n.jsonl.gz --minutes=$mi --rng=$r --seedfile=$sf "$@" >> $H/$n.log 2>&1
