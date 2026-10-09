#!/bin/bash
# The runs behind NOTES.md, one process at a time (logs in logs/). The last line (LS on every profile with n = 4,
# m = 6) was NOT run in the exploration session (time box).
cd "$(dirname "$0")"
python3 exp_objectives.py 3 6 3 7 > logs/objectives_n3.log 2>&1
{ for m in 3 4 5 6; do python3 exp_fast.py small 2 $m; done
  for m in 4 5 6 7; do python3 exp_fast.py small 3 $m; done; } > logs/fast_small_n23.log 2>&1
python3 exp_fast.py small 4 5 > logs/fast_4_5.log 2>&1
python3 exp_fast.py small 4 6 > logs/fast_4_6.log 2>&1                        # about 6 minutes
python3 exp_fast.py cores 5 200 5 pareto,minNA,sumU > logs/fast_cores5.log 2>&1
{ for m in 3 4 5 6; do python3 ls.py small 2 $m minexp; done
  for m in 4 5 6 7; do python3 ls.py small 3 $m minexp; done
  python3 ls.py small 4 5 minexp; } > logs/ls_small.log 2>&1
python3 ls.py cores 5 200 5 minexp > logs/ls_cores5_minexp.log 2>&1         # 2 failures (absorber rule)
python3 ls.py cores 5 200 5 > logs/ls_cores5.log 2>&1                       # rule mindef
python3 ls.py random 20000 1 8 > logs/ls_random8.log 2>&1
{ for m in 3 4 5 6; do python3 exp_local.py small 2 $m; done
  for m in 4 5 6 7; do python3 exp_local.py small 3 $m; done
  python3 exp_local.py small 4 5; } > logs/stuck_small.log 2>&1
python3 exp_local.py random 2000 2 5 > logs/stuck_random5.log 2>&1
{ python3 exp_stuck_cases.py small 3 7; python3 exp_stuck_cases.py random 4000 3 5; } > logs/stuck_cases.log 2>&1
# not run yet:
# python3 ls.py small 4 6 > logs/ls_4_6.log 2>&1
