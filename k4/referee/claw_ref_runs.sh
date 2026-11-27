#!/bin/sh
# Referee runs for K4.MC9 (k4/referee/twins.md addendum 2; log results/k4_referee/claw_ref.log).
# $1: a directory with results/k4_twins/{claw,claw_y12,claw_y123}.json.gz from proof/k4-twins-2 (ea71fb54).
cd "$(dirname "$0")"; D=$1; T=${TMPDIR:-/tmp}
python3 claw_ref.py shapes $D/claw.json.gz,$D/claw_y12.json.gz
python3 claw_ref.py $D/claw.json.gz 150 1 claw > $T/cl1.out &
python3 claw_ref.py $D/claw_y12.json.gz 150 2 claw-y12 > $T/cl2.out &
python3 claw_ref.py $D/claw_y123.json.gz 150 3 claw-y123 > $T/cl3.out &
python3 claw_ref.py $D/claw.json.gz,$D/claw_y12.json.gz 20 9 claw,claw-y12 interior > $T/cl4.out &   # mutation (must fail)
wait
cat $T/cl1.out $T/cl2.out $T/cl3.out $T/cl4.out
