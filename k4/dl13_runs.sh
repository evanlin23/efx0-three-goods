#!/bin/sh
# The DL13 runs of compute/k4-dl13 (results/k4_dl13/; ledger K4.DL2.T13, K4.DL2.T13X). Two worker processes.
# Every run is resumable: rerun the same command after a kill (per-unit checkpoints results/k4_dl13/ckpt_*.jsonl;
# the logs are appended to, so a log may show a restart). Usage: sh k4/dl13_runs.sh STEP   (STEP below)
# The n = 4 certificate runs (classes with one and two 4-good agents exhaustively, three and four sampled) are made
# by the branch compute/k4-dl13-n4 with the same tools (results/k4_dl13/n4_*.log there).
set -e
cd "$(dirname "$0")/.."
R=results/k4_dl13
G=results/k4_gap                       # #53's catalogues and hunts as on main
mkdir -p $R
run() { python3 k4/dl13_run.py "$@"; }
case "$1" in
check)          # cross-checks of dl13.c (k4/dl13_check.py: dl2_relations.py, c4x_check.py + rel_B, dl2.c's K line, hash build)
  python3 k4/dl13_check.py suite > $R/check_suite.log 2>&1
  python3 k4/dl13_check.py certs results/k4_certs_3.json.gz --rand=40 --seed=13 > $R/check_rand_n3.log 2>&1
  python3 k4/dl13_check.py catalog $G/gap_n3.json.gz --every=40 > $R/check_cat_gap_n3.log 2>&1
  python3 k4/dl13_check.py records $R/states_n3.jsonl.gz --every=10 > $R/check_states_n3.log 2>&1
  for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 gap_n4_pure_s4000; do
    python3 k4/dl13_check.py catalog $G/$c.json.gz --every=200 > $R/check_cat_${c}.log 2>&1; done
  python3 k4/dl13_check.py catalog $G/hard_hunt.json.gz > $R/check_cat_hard_hunt.log 2>&1
  for c in gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100; do
    python3 k4/dl13_check.py catalog $G/$c.json.gz --every=500 --no-x > $R/check_cat_${c}.log 2>&1; done
  ;;
same)           # dl13u.c (the source of the n <= 3 run and the hunts) gives dl13.c's output
  python3 k4/dl13u_same.py suite > $R/same_suite.log 2>&1
  python3 k4/dl13u_same.py certs results/k4_certs_2.json.gz > $R/same_n2.log 2>&1
  python3 k4/dl13u_same.py certs results/k4_certs_3.json.gz --cores=0:41 --progress > $R/same_n3_0_40.log 2>&1
  python3 k4/dl13u_same.py catalog $G/gap_n4_pure_s4000.json.gz --every=10 > $R/same_gap_n4_pure.log 2>&1
  ;;
n3)             # every profile of every core with n <= 3 and a 4-good agent (about 30 min; made with the source now in
                # k4/dl13u.c, see k4/dl13u_same.py: add --src=dl13u.c to rerun with it)
  run certs results/k4_certs_2.json.gz results/k4_certs_3.json.gz --jobs=2 --rt=100 --ckpt=$R/ckpt_n3.jsonl \
      --dump=$R/states_n3.jsonl.gz --tables=$R/tables_n3.json --progress >> $R/n3.log 2>&1 ;;
cat)            # #53's n = 4 and n = 5 catalogues and hunts and the hard hunt, every record (gap profiles, f >= 1)
  for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 gap_n4_pure_s4000 hard_hunt hunt_n4_2_all hunt_n4_3_s400k \
           hunt_n4_pure_s400k gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100 hunt_n5_3_s2000 \
           hunt_n5_4_s2000 hunt_n5_pure_s2000; do
    run catalog $G/$c.json.gz --jobs=${J:-1} --rt=5 --ro=200 --ckpt=$R/ckpt_cat.jsonl --dump=$R/states_cat.jsonl.gz \
        --tables=$R/tables_cat_$c.json >> $R/cat_$c.log 2>&1
  done ;;
esac
