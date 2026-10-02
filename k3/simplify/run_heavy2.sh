#!/bin/bash
# K3S on random profiles of the certified cores with n = 6, 7, 8 (logs: results/k3_simplify/, or $LOGDIR then copied)
cd "$(dirname "$0")"; OUT=../../results/k3_simplify; L=${LOGDIR:-$OUT}
{ time python3 test_k3s.py coresample 300 6 6 results/certs_lb_2_6.json.gz results/certs_lb_disconnected_4_6.json.gz ; } > $L/k3s_cores_6_sample.log 2>&1
{ time python3 test_k3s.py coresample 20 7 7 results/certs_lb_7_3_7.json.gz results/certs_lb_7_8.json.gz results/certs_lb_7_9.json.gz results/certs_lb_7_10.json.gz results/certs_lb_7_11_14.json.gz ; } > $L/k3s_cores_7_sample.log 2>&1
{ time python3 test_k3s.py coresample 100 8 8 results/certs_lb_8_14.json.gz results/certs_lb_8_15_16.json.gz ; } > $L/k3s_cores_8_sample.log 2>&1
[ "$L" != "$OUT" ] && for f in k3s_cores_6_sample k3s_cores_7_sample k3s_cores_8_sample; do cp $L/$f.log $OUT/; done
true
