#!/bin/bash
# The runs of k4/c4min_hunt.md, one section per log (run from the repository root): bash k4/c4min_hunt_runs.sh SECTION
# Every log starts with the command, the commit and the sha1 of k4/c4min_hunt.c, and ends with the finishing time.
set -e
cd "$(dirname "$0")/.."
R=results
log() {  # log FILE COMMAND...
  local f=$1; shift
  { echo "# command: $*"; echo "# commit $(git rev-parse --short HEAD), k4/c4min_hunt.c sha1 $(sha1sum k4/c4min_hunt.c | cut -c1-12), started $(date -u)";
    (cd k4 && "$@") 2>&1 || echo "# exit status $?"; echo "# finished $(date -u)"; } >> "$f"
}
case "$1" in
  selfcheck)   # every profile of n <= 3 and of n = 4 with one or two 4-good agents re-solved from scratch (-V); and the
               # profiles with the first agent's first type of 12 pure n = 4 cores and 40 n = 5 cores (three 4-good agents)
    log $R/k4_c4min_hunt_selfcheck.log python3 c4min_hunt_run.py ../$R/k4_certs_2.json.gz ../$R/k4_certs_3.json.gz \
        ../$R/k4_certs_4_n4_1.json.gz ../$R/k4_certs_4_n4_2.json.gz -V
    log $R/k4_c4min_hunt_selfcheck.log python3 c4min_hunt_run.py ../$R/k4_certs_4_pure.json.gz --order=big --best=1 \
        --only=0,20,40,60,80,100,120,140,160,180,200,218 --first=1 -V
    log $R/k4_c4min_hunt_selfcheck.log python3 c4min_hunt_run.py ../$R/k4_certs_5_n4_3.json.gz --order=big \
        --only=$(seq -s, 0 250 9860) --first=1 -V ;;
  w0small)     # the variant with the owner's needs from its base: must find PR #36's 720 profiles at n = 2
    log $R/k4_c4min_hunt_w0.log python3 c4min_hunt_run.py ../$R/k4_certs_2.json.gz ../$R/k4_certs_3.json.gz \
        ../$R/k4_certs_4_n4_1.json.gz ../$R/k4_certs_4_n4_2.json.gz -w0 ;;
  w0big)       # the -w0 variant on the larger exhaustive classes
    log $R/k4_c4min_hunt_w0.log python3 c4min_hunt_run.py ../$R/k4_certs_4_n4_3.json.gz ../$R/k4_certs_5_n4_1.json.gz \
        ../$R/k4_certs_5_n4_2.json.gz -w0 --jobs=${JOBS:-4}
    log $R/k4_c4min_hunt_w0.log python3 c4min_hunt_run.py ../$R/k4_certs_4_pure.json.gz --order=big --best=1 -w0 --jobs=${JOBS:-4} ;;
  classes)     # n = 5 with four or five 4-good agents, every 4-good agent restricted to two order-type classes
               # (k4/c4min_common.py type_class): 10,11 = 'a > b + c' (G1 of k4/c4x.md §5); 0,1 = flat (a < c + d, G4)
    for cl in ${CLS:-10,11 0,1}; do
      log $R/k4_c4min_hunt_classes.log python3 c4min_hunt_run.py ../$R/k4_certs_5_n4_4.json.gz ../$R/k4_certs_5_pure.json.gz \
          --classes=$cl --jobs=${JOBS:-4}
    done ;;
  crosscheck)  # three implementations on random profiles
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_2.json.gz --per-core=40 --seed=1
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_3.json.gz --per-core=10 --seed=2
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_4_n4_1.json.gz ../$R/k4_certs_4_n4_2.json.gz \
        ../$R/k4_certs_4_n4_3.json.gz ../$R/k4_certs_4_pure.json.gz --per-core=2 --seed=3
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_5_n4_1.json.gz ../$R/k4_certs_5_n4_2.json.gz \
        ../$R/k4_certs_5_n4_3.json.gz ../$R/k4_certs_5_n4_4.json.gz ../$R/k4_certs_5_pure.json.gz --cores=100 --per-core=2 --seed=4
    log $R/k4_c4min_hunt_crosscheck.log python3 c4min_crosscheck.py ../$R/k4_certs_3.json.gz ../$R/k4_certs_4_pure.json.gz \
        --w0 --per-core=2 --seed=5 ;;
  n4)          # n = 4 with three 4-good agents, and pure n = 4: every strict profile (pure: one agent with the most
               # types first, one certificate per solve: faster there)
    log $R/k4_c4min_hunt_n4_3.log python3 c4min_hunt_run.py ../$R/k4_certs_4_n4_3.json.gz --ckpt=../$R/k4_c4min_hunt_n4_3.ckpt
    log $R/k4_c4min_hunt_n4_pure.log python3 c4min_hunt_run.py ../$R/k4_certs_4_pure.json.gz --order=big --best=1 \
        --ckpt=../$R/k4_c4min_hunt_n4_pure.ckpt ;;
  n5a)         # n = 5 with one or two 4-good agents: every strict profile
    log $R/k4_c4min_hunt_n5_12.log python3 c4min_hunt_run.py ../$R/k4_certs_5_n4_1.json.gz ../$R/k4_certs_5_n4_2.json.gz \
        --ckpt=../$R/k4_c4min_hunt_n5_12.ckpt ;;
  n5b)         # n = 5 with three 4-good agents: every strict profile (long; resumes from the checkpoint)
    log $R/k4_c4min_hunt_n5_3.log python3 c4min_hunt_run.py ../$R/k4_certs_5_n4_3.json.gz --jobs=${JOBS:-4} \
        --ckpt=../$R/k4_c4min_hunt_n5_3.ckpt ;;
  n6a)         # n = 6 with exactly one 4-good agent: every strict profile
    log $R/k4_c4min_hunt_n6_1.log python3 c4min_hunt_run.py ../$R/k4_certs_6_n4_1.json.gz --jobs=${JOBS:-4} \
        --ckpt=../$R/k4_c4min_hunt_n6_1.ckpt ;;
  climb5)      # hill-climbing on every n = 5 core with four or five 4-good agents
    log $R/k4_c4min_hunt_climb_n5_45.log python3 c4min_climb.py --file=../$R/k4_certs_5_n4_4.json.gz \
        --file=../$R/k4_certs_5_pure.json.gz --iters=3000 --restarts=3 --order=0 --seed=51 --jobs=${JOBS:-1} --top=20 ;;
  climb5b)     # the other objective orders (with annealing), more restarts, and PR #30's eight n = 5 GM4 profiles as starts;
               # every core's best goes to a dump, from which climbtight picks the tightest cores
    log $R/k4_c4min_hunt_climb_n5_b.log python3 c4min_climb.py --file=../$R/k4_certs_5_n4_4.json.gz \
        --file=../$R/k4_certs_5_pure.json.gz --iters=3000 --restarts=6 --order=1 --seed=52 --jobs=${JOBS:-4} --top=20 \
        --dump=../$R/k4_c4min_hunt_climb_n5_b.jsonl
    log $R/k4_c4min_hunt_climb_n5_b.log python3 c4min_climb.py --file=../$R/k4_certs_5_n4_4.json.gz \
        --file=../$R/k4_certs_5_pure.json.gz --iters=4000 --restarts=4 --order=2 --anneal=30 --stale=800 --seed=54 --jobs=${JOBS:-4} --top=20 \
        --dump=../$R/k4_c4min_hunt_climb_n5_b.jsonl
    log $R/k4_c4min_hunt_climb_n5_b.log python3 c4min_climb.py --seeds=../$R/k4_c4min_hunt_seeds_gm4.json \
        --iters=20000 --restarts=20 --order=0 --seed=53 --jobs=${JOBS:-4} --top=8 ;;
  climbtight)  # the 400 tightest n = 5 cores of climb5b (an owner needed; highest d*, then fewest witnesses), climbed harder
    python3 -c "
import json
best = {}
for l in open('$R/k4_c4min_hunt_climb_n5_b.jsonl'):
    r = json.loads(l)
    if not r['owner']: continue
    k = (r['file'], r['core']); key = (r['dstar'], -r['good'])
    if k not in best or key > best[k][0]: best[k] = (key, l)
top = sorted(best.values(), key=lambda x: x[0], reverse=True)[:400]
with open('$R/k4_c4min_hunt_tight_n5.jsonl', 'w') as out:
    for _, l in top: out.write(l)
print(len(top), 'tight cores; scores from', top[0][0], 'to', top[-1][0])"
    log $R/k4_c4min_hunt_climb_tight.log python3 c4min_climb.py --file=../$R/k4_certs_5_n4_4.json.gz \
        --file=../$R/k4_certs_5_pure.json.gz --cores=../$R/k4_c4min_hunt_tight_n5.jsonl --iters=10000 --restarts=20 \
        --order=0 --anneal=20 --stale=2000 --seed=55 --jobs=${JOBS:-4} --top=20 ;;
  climbrand)   # random connected cores, n = 6-8
    for nmk in 6:9:3 6:12:4 6:14:6 6:16:6 7:12:4 7:15:7 7:18:7 8:14:5 8:17:8 8:20:8; do
      log $R/k4_c4min_hunt_climb_rand.log python3 c4min_climb.py --random=$nmk:60 --iters=2000 --restarts=2 \
          --order=0 --seed=61 --jobs=${JOBS:-4} --top=3
    done ;;
  climbglue)   # two cores joined by a good or by a connector agent
    for spec in 3:3 3:4_pure 4_pure:4_pure 3:4_n4_3; do
      a=${spec%%:*}; b=${spec##*:}
      for mode in merge link link3; do
        log $R/k4_c4min_hunt_climb_glue.log python3 c4min_climb.py --glue=../$R/k4_certs_$a.json.gz:../$R/k4_certs_$b.json.gz:40:$mode \
            --iters=2000 --restarts=2 --order=0 --seed=71 --jobs=${JOBS:-4} --top=3
      done
    done ;;
  rigid)       # owner-rigid gadgets glued in pairs
    log $R/k4_c4min_hunt_rigid.log python3 c4min_rigid.py ../$R/k4_certs_3.json.gz --samples=400 --pairs=150 --seed=81 --jobs=${JOBS:-4}
    log $R/k4_c4min_hunt_rigid.log python3 c4min_rigid.py ../$R/k4_certs_4_n4_3.json.gz ../$R/k4_certs_4_pure.json.gz \
        --samples=60 --pairs=80 --seed=82 --jobs=${JOBS:-4} ;;
  rigid5)      # pairs of the tightest n = 5 profiles of climb5b (owner needed, d* = 0) glued (n = 10-11)
    log $R/k4_c4min_hunt_rigid.log python3 c4min_rigid.py --gadgets=../$R/k4_c4min_hunt_climb_n5_b.jsonl --pairs=200 --seed=83 \
        --jobs=${JOBS:-4} ;;
  families)    # structured families: random and perturbed profiles (exact test per profile); m <= 64
    for fam in ${FAMS:-ht:4 ht:5 ht2:4 htx:4 htc:4 grid:2:2 chain:2:2 ht:6 cycle:4 tree:4}; do
      log $R/k4_c4min_hunt_families.log python3 c4min_sample.py --family=$fam --profiles=400 --mode=uniform --seed=91 --verify=20 --jobs=1
    done
    for k in 1 2 4 8; do
      log $R/k4_c4min_hunt_families.log python3 c4min_sample.py --family=ht:4 --family=ht:5 --family=htc:4 --profiles=400 \
          --mode=perturb:$k --seed=92 --verify=10 --jobs=${JOBS:-4}
    done ;;
  climbfam)    # hill-climbing on the smaller family members (objective: owner needed, f*, fewest witnesses up to 200)
    log $R/k4_c4min_hunt_climb_fam.log python3 c4min_climb.py --family=ht:2 --family=ht:3 --family=ht2:3 --family=htx:3 \
        --family=htc:2 --family=htc:3 --family=cycle:2 --family=tree:2 --start=paper --iters=1500 --restarts=3 --order=2 --cap=200 \
        --seed=101 --jobs=${JOBS:-4} --top=8 ;;
  attempts)    # the hard profiles of PR #36's attempts and PR #30's n = 5 GM4 profiles, one by one
    log $R/k4_c4min_hunt_attempts.log python3 c4min_attempts_eval.py ;;
  *) echo "sections: rigid5 classes w0big attempts climbtight selfcheck w0small crosscheck n4 n5a n5b n6a climb5 climb5b climbrand climbglue rigid families climbfam"; exit 2 ;;
esac
