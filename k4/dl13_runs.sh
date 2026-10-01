#!/bin/sh
# The DL13 runs of compute/k4-dl13 (results/k4_dl13/; ledger K4.DL2.T13, K4.DL2.T13X). Two worker processes.
# Every run is resumable: rerun the same command after a kill (per-unit checkpoints results/k4_dl13/ckpt_*.jsonl;
# the logs are appended to, so a log may show a restart). Usage: sh k4/dl13_runs.sh STEP   (STEP below)
# The checkpoints are resume aids only: ckpt_cat.jsonl and ckpt_rand.jsonl are not committed (too large); the summary is
# rebuilt from the committed tables_*.json (step summary).
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
  python3 k4/dl13_check.py catalog $G/hard_hunt.json.gz --no-x > $R/check_cat_hard_hunt.log 2>&1    # c4x_check: too slow at m = 12
  for c in gap_n5_2_s100 gap_n5_3_s100 gap_n5_4_s100 gap_n5_pure_s100; do
    python3 k4/dl13_check.py catalog $G/$c.json.gz --every=500 --no-x > $R/check_cat_${c}.log 2>&1; done
  ;;
same)           # dl13u.c (the source of the n <= 3 run and the hunts) gives dl13.c's output
  python3 k4/dl13u_same.py suite > $R/same_suite.log 2>&1
  python3 k4/dl13u_same.py certs results/k4_certs_2.json.gz > $R/same_n2.log 2>&1
  python3 k4/dl13u_same.py catalog $G/gap_n4_pure_s4000.json.gz --every=10 > $R/same_gap_n4_pure.log 2>&1
  # every profile of the n = 3 cores 0..32 (all but the 18 largest), with the n <= 3 run's options, default builds
  python3 k4/dl13u_same.py certs results/k4_certs_3.json.gz --cores=0:33 --copts=-r100,-o0 --nohash --progress \
      > $R/same_n3_0_32.log 2>&1
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
rand)           # random strict profiles: every n = 5 core 4 each, every n = 6 core with one 4-good agent 2 each
  for f in 5_n4_1 5_n4_2 5_n4_3 5_n4_4 5_pure; do
    run certs results/k4_certs_$f.json.gz --sample=4 --seed=1 --jobs=${J:-1} --rt=1 --ro=1000 --ckpt=$R/ckpt_rand.jsonl \
        --dump=$R/states_rand.jsonl.gz --tables=$R/tables_rand_$f.json >> $R/rand_$f.log 2>&1
  done
  run certs results/k4_certs_6_n4_1.json.gz --sample=2 --seed=1 --jobs=${J:-1} --rt=1 --ro=1000 --ckpt=$R/ckpt_rand.jsonl \
      --dump=$R/states_rand.jsonl.gz --tables=$R/tables_rand_6_n4_1.json >> $R/rand_6_n4_1.log 2>&1 ;;
ht)             # H_2 of k4/c4.md §7 (n = 9) with §7's values and 200 random strict profiles; H_3 (n = 13, m = 33)
  run ht 2 --jobs=1 --rt=1 --ro=20 --dump=$R/states_ht.jsonl.gz --tables=$R/tables_h2.json >> $R/h2.log 2>&1
  run ht 2 --sample=200 --seed=1 --jobs=${J:-1} --rt=1 --ro=50 --ckpt=$R/ckpt_ht.jsonl --dump=$R/states_ht.jsonl.gz \
      --tables=$R/tables_h2_s200.json >> $R/h2_s200.log 2>&1 ;;
summary)        # results/k4_dl13/summary.md: every run, and T1 / T3 by obstruction class per group of inputs
  T=$R/tables
  python3 k4/dl13_summary.py --distinct-fail=7154 \
    "--note=Distinct failing states (f ≥ 1, DL13 fails) over these inputs: 7,154. The sum row counts 7,155 because the failing state of gap_n4_pure_s4000 (dl13-n4m9-rot) is also a state of the neighbourhood run; in general the hunts and samples may repeat profiles." \
    "--note=n3.log's header labels its binary 'dl13.c sha256 e5ab32ae…': that run used the source now in k4/dl13u.c (dl13.c plus the hunts' slack line and a dedupe of hashed candidates), output-identical to dl13.c (sha256 f891de3a…) without -v; see k4/dl13u_same.py and results/k4_dl13/same_*.log." \
    "--note=The commands below name checkpoint files (--ckpt=…): they are resume aids only. ckpt_cat.jsonl and ckpt_rand.jsonl are not committed (too large); this summary is rebuilt from the committed tables_*.json (sh k4/dl13_runs.sh summary)." \
    "@n <= 3, every profile (exhaustive)" "n <= 3=${T}_n3.json" \
    "@n = 4, one and two 4-good agents, every profile (exhaustive; compute/k4-dl13-n4)" "n4_1=${T}_n4_1.json" "n4_2=${T}_n4_2.json" \
    "@n = 4, three and four 4-good agents, 200 random profiles per core, seeds 1, 2 (compute/k4-dl13-n4)" \
      "n4_3 s1=${T}_n4_3_s200.json" "n4_3 s2=${T}_n4_3_s200b.json" "pure s1=${T}_n4_pure_s200.json" "pure s2=${T}_n4_pure_s200b.json" \
    "@#53's n = 4 and n = 5 catalogues and hunts, every record" $(for c in gap_n4_1 gap_n4_2_s4000 gap_n4_3_s4000 \
      gap_n4_pure_s4000 hard_hunt hunt_n4_2_all hunt_n4_3_s400k hunt_n4_pure_s400k gap_n5_1_s100 gap_n5_2_s100 gap_n5_3_s100 \
      gap_n5_4_s100 gap_n5_pure_s100 hunt_n5_3_s2000 hunt_n5_4_s2000 hunt_n5_pure_s2000; do echo "$c=${T}_cat_$c.json"; done) \
    "@adversarial: the neighbourhood of dl13-n4m9-rot and the hunts" "nbhd core 123=${T}_nbhd123.json" \
      $(for c in hunt_pure_m8 hunt_n4_3_m8 hunt_pure_m6 hunt_n4_3_m6 hunt_gap_n5_pure_s100 hunt_gap_n5_4_s100 hunt_gap_n5_3_s100; do echo "$c=${T}_$c.json"; done) \
    "@random n = 5, 6 profiles and H_2" $(for c in rand_5_n4_1 rand_5_n4_2 rand_5_n4_3 rand_5_n4_4 rand_5_pure rand_6_n4_1 h2 h2_s200; do echo "$c=${T}_$c.json"; done) \
    > $R/summary.md ;;
fails)          # every DL13 failure found, re-derived with model.py, with the candidate relations (R_134, R_T + T4, ...)
  python3 k4/dl13_fails.py $R/dump_n4_1.jsonl.gz $R/dump_n4_2.jsonl.gz $R/dump_n4_3_s200b.jsonl.gz $R/states_cat.jsonl.gz \
      $R/states_nbhd123.jsonl.gz $R/hunt_n4_3_m8.jsonl.gz $R/hunt_pure_m8.jsonl.gz $R/hunt_n4_3_m6.jsonl.gz \
      $R/hunt_pure_m6.jsonl.gz $R/hunt_n5.jsonl.gz --out=$R/fails_all.jsonl.gz > $R/fails_all.log 2>&1 ;;
xcheck134)      # T4 / R_134 / R_T + T4 on c4x_check.py (no model.py): the n = 4 certificate-run failures, this branch's, n = 5
  python3 k4/dl134_xcheck.py $R/dump_n4_1.jsonl.gz $R/dump_n4_2.jsonl.gz $R/dump_n4_3_s200b.jsonl.gz \
      --out=$R/dl134_xcheck_n4.jsonl.gz > $R/dl134_xcheck_n4.log 2>&1
  python3 k4/dl134_xcheck.py $R/states_cat.jsonl.gz $R/states_nbhd123.jsonl.gz $R/hunt_n4_3_m8.jsonl.gz $R/hunt_pure_m8.jsonl.gz \
      $R/hunt_n4_3_m6.jsonl.gz $R/hunt_pure_m6.jsonl.gz --out=$R/dl134_xcheck_own.jsonl.gz > $R/dl134_xcheck_own.log 2>&1
  python3 k4/dl134_xcheck.py $R/hunt_n5.jsonl.gz --out=$R/dl134_xcheck_n5.jsonl.gz > $R/dl134_xcheck_n5.log 2>&1 ;;
h3)
  run ht 3 --wide --jobs=1 --rt=1 --ro=20 --dump=$R/states_ht.jsonl.gz --tables=$R/tables_h3.json >> $R/h3.log 2>&1 ;;
esac
