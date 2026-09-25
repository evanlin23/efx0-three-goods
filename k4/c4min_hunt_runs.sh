#!/bin/bash
# The runs of k4/c4min_hunt.md, one section per log (run from the repository root): bash k4/c4min_hunt_runs.sh SECTION
# Every log starts with the command, the commit and the sha1 of k4/c4min_hunt.c, and ends with the finishing time.
set -e
cd "$(dirname "$0")/.."
R=results
log() {  # log FILE COMMAND...
  local f=$1; shift
  { echo "# command: $*"; echo "# commit $(git rev-parse --short HEAD), k4/c4min_hunt.c sha1 $(sha1sum k4/c4min_hunt.c | cut -c1-12), started $(date -u)";
    (cd k4 && "$@") 2>&1; echo "# finished $(date -u)"; } >> "$f"
}
case "$1" in
  selfcheck)   # every profile of n <= 3 and of n = 4 with one or two 4-good agents re-solved from scratch (-V)
    log $R/k4_c4min_hunt_selfcheck.log python3 c4min_hunt_run.py ../$R/k4_certs_2.json.gz ../$R/k4_certs_3.json.gz \
        ../$R/k4_certs_4_n4_1.json.gz ../$R/k4_certs_4_n4_2.json.gz -V ;;
  w0small)     # the variant with the owner's needs from its base: must find PR #36's 720 profiles at n = 2
    log $R/k4_c4min_hunt_w0.log python3 c4min_hunt_run.py ../$R/k4_certs_2.json.gz ../$R/k4_certs_3.json.gz \
        ../$R/k4_certs_4_n4_1.json.gz ../$R/k4_certs_4_n4_2.json.gz -w0 ;;
  crosscheck)  # three implementations on random profiles
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_2.json.gz --per-core=40 --seed=1
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_3.json.gz --per-core=10 --seed=2
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_4_n4_1.json.gz ../$R/k4_certs_4_n4_2.json.gz \
        ../$R/k4_certs_4_n4_3.json.gz ../$R/k4_certs_4_pure.json.gz --per-core=2 --seed=3
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_5_n4_1.json.gz ../$R/k4_certs_5_n4_2.json.gz \
        ../$R/k4_certs_5_n4_3.json.gz ../$R/k4_certs_5_n4_4.json.gz ../$R/k4_certs_5_pure.json.gz --cores=100 --per-core=2 --seed=4
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_3.json.gz ../$R/k4_certs_4_pure.json.gz \
        --w0 --per-core=2 --seed=5 ;;
  n4)          # n = 4 with three 4-good agents, and pure n = 4: every strict profile
    log $R/k4_c4min_hunt_n4_3.log python3 c4min_hunt_run.py ../$R/k4_certs_4_n4_3.json.gz --ckpt=../$R/k4_c4min_hunt_n4_3.ckpt
    log $R/k4_c4min_hunt_n4_pure.log python3 c4min_hunt_run.py ../$R/k4_certs_4_pure.json.gz --ckpt=../$R/k4_c4min_hunt_n4_pure.ckpt ;;
  n5a)         # n = 5 with one or two 4-good agents: every strict profile
    log $R/k4_c4min_hunt_n5_12.log python3 c4min_hunt_run.py ../$R/k4_certs_5_n4_1.json.gz ../$R/k4_certs_5_n4_2.json.gz \
        --ckpt=../$R/k4_c4min_hunt_n5_12.ckpt ;;
  n5b)         # n = 5 with three 4-good agents: every strict profile (long; resumes from the checkpoint)
    log $R/k4_c4min_hunt_n5_3.log python3 c4min_hunt_run.py ../$R/k4_certs_5_n4_3.json.gz --jobs=${JOBS:-4} \
        --ckpt=../$R/k4_c4min_hunt_n5_3.ckpt ;;
  *) echo "sections: selfcheck w0small crosscheck n4 n5a n5b"; exit 2 ;;
esac
