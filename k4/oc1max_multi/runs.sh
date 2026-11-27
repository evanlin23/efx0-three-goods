#!/bin/sh
# Reproduce the data of k4/oc1max_multi.md §1 (run from the repository root; about 4 minutes on 4 CPUs).
set -e
R=results/k4_oc1max_multi; mkdir -p $R
rm -f $R/hard2_starts.jsonl $R/hard2_starts.jsonl.gz
for s in special screen suite logs; do OUT=$R/hard2_starts.jsonl python3 k4/oc1max_multi/collect.py $s; done > $R/collect.log
OUT=$R/hard2_starts.jsonl python3 k4/oc1max_multi/collect.py cores:k4_certs_2.json.gz,k4_certs_3.json.gz 3000 91 >> $R/collect.log
OUT=$R/hard2_starts.jsonl python3 k4/oc1max_multi/collect.py cores:k4_certs_4_n4_1.json.gz,k4_certs_4_n4_2.json.gz,k4_certs_4_n4_3.json.gz,k4_certs_4_pure.json.gz 1500 92 >> $R/collect.log
OUT=$R/hard2_starts.jsonl python3 k4/oc1max_multi/collect.py cores:k4_certs_5_n4_1.json.gz,k4_certs_5_n4_2.json.gz 150 93 >> $R/collect.log
OUT=$R/hard2_starts_n5.jsonl python3 k4/oc1max_multi/collect.py n5:n4_3,n4_4,pure,n4_1,n4_2 1 17 > $R/collect_n5.log
gzip -f $R/hard2_starts.jsonl $R/hard2_starts_n5.jsonl
