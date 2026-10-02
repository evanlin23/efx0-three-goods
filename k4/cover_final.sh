#!/bin/sh
# Final summaries of workstream compute/k4-cover (results/k4_cover/SUMMARY.md is written from these).
R=results/k4_cover
V=$R/validate; C=$R/checks; F=$R/f2; H=$R/hunt
python3 k4/cover_summary.py \
  "validate_f1=$V/f1_n3_all.jsonl.gz,$V/f1_n4_hunts_p*.jsonl.gz,$V/f1_n5_hunts.jsonl.gz,$V/f1_rc45.jsonl.gz,$V/f1_t1stuck.jsonl.gz" \
  > $R/final_validate_f1.txt
python3 k4/cover_summary.py --nodedup "validate_f2=$V/f2_cat.jsonl.gz,$V/f2_t1stuck.jsonl.gz,$V/f2_n5c.jsonl.gz" > $R/final_validate_f2.txt
python3 k4/cover_summary.py \
  "n3_every_profile=$C/n3_all_f2_p*.jsonl.gz" \
  "n4_1_every_profile=$C/n4_1_all_p*.jsonl.gz" \
  "n4_2_every_profile=$C/n4_2_all_p*.jsonl.gz" \
  "n4_3_200k_per_core=$C/n4_3_r200k_p*.jsonl.gz" \
  "n4_pure_2k_and_200k_per_core=$C/n4_pure_r2k_p*.jsonl.gz,$C/n4_pure_r200k_p*.jsonl.gz" \
  "n5_200_per_core=$C/n5_n4_1_r200_p*.jsonl.gz,$C/n5_n4_2_r200_p*.jsonl.gz,$C/n5_n4_3_r200_p*.jsonl.gz,$C/n5_n4_4_r200_p*.jsonl.gz,$C/n5_pure_r200_p*.jsonl.gz,$C/n5_pure_bt_r200_p*.jsonl.gz" \
  "n5_2k_per_core=$C/n5_n4_4_r2k_p*.jsonl.gz,$C/n5_pure_r2k_p*.jsonl.gz,$C/n5_pure_bt_r2k_p*.jsonl.gz" \
  "dumps=$F/dumps_p*.jsonl.gz,$F/dumps5_p*.jsonl.gz,$F/rest_p*.jsonl.gz,$F/n6s_p*.jsonl.gz,$F/n6r_p*.jsonl.gz" \
  > $R/final_phase2.txt
python3 k4/cover_summary.py \
  "ALL=$V/f1_*.jsonl.gz,$V/f2_*.jsonl.gz,$C/*.jsonl.gz,$F/*.jsonl.gz,$H/*.jsonl.gz" > $R/final_all.txt
python3 k4/cover_uncovered.py $R/uncovered_keys.jsonl.gz $C/*.jsonl.gz $F/*.jsonl.gz $H/*.jsonl.gz --maxn=5 > $R/uncovered_keys.log 2>&1
