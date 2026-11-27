#!/bin/sh
# one-step-lemma candidates with rotations along cycles as single moves, steps of at most two moves
# (k4/haxell.md §6); logs in results/k4_haxell/
cd "$(dirname "$0")"
L=../../results/k4_haxell
cc -O2 -o gstar_measure gstar_measure.c 2>/dev/null
for spec in "screen NMAX=4 MMAX=7 MAXSTATES=400000" "suite NMAX=4 MMAX=7 MAXSTATES=400000" \
            "gen:800:33:3:6:3 NMAX=3 MMAX=6" "gen:800:34:3:6:4 NMAX=3 MMAX=6" "gen:3000:15:2:5:5 NMAX=2 MMAX=6" \
            "cores:k4_certs_2.json.gz,k4_certs_3.json.gz:600:7 NMAX=3 MMAX=7" "gen:600:55:3:7:5 NMAX=3 MMAX=7" \
            "gen:300:57:4:7:4 NMAX=4 MMAX=7" "gen:300:58:4:7:7 NMAX=4 MMAX=7" "ext NMAX=5 MMAX=9 MAXSTATES=11000000" \
            "ttc NMAX=5 MMAX=9 MAXSTATES=11000000"; do
  tag=$(echo $spec | cut -d' ' -f1 | tr ':,' '__' | cut -c1-40)
  python3 gstar_measure_run.py $spec RADIUS=2 ROT=1 > $L/measure_rot2_$tag.log 2>&1
done
echo ALLDONE > $L/measure_rot_done.flag
