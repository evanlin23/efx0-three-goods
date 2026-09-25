#!/bin/sh
# The counts quoted for the rejected LB4 variants (attempts/lb4-*.md, k4/lb4.md §3), with the exact options of
# k4/lb4.c. Output: results/k4_lb4_variants.log (each block starts with the command line, printed by lb4_run.py).
# Not here, each in its own log with its command line: -i8 (results/k4_lb4_i8.log), -i9 (results/k4_lb4_i9_run.log),
# and nested rotations beyond n = 3 (results/k4_lb4_nested_n4.log, _pure4.log, _n5.log, _every.log).
# Usage (from the repository root): sh k4/lb4_variant_runs.sh > results/k4_lb4_variants.log 2>&1      (~1 h, 4 CPUs)
R=results
run() { python3 k4/lb4_run.py "$@" --show=3; }
echo "## LB+'s shape (attempts/lb4-lbplus-shape.md)"
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i0 -u1 -o2 -r1
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i0 -u2 -o2 -r1
echo "## no rotation (attempts/lb4-no-rotation.md)"
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i2 -u3 -r0 -w1
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i2 -u1 -r0 -w1 -c1
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i9 -u1 -r0 -w1 -c1
echo "## fixed insertion rules, one rotation (attempts/lb4-fixed-insertion.md)"
for i in -i0 -i3 -i4 -i5 -i7; do run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz $i -u1 -r1 -w1 -c1; done
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i0 -u3 -r1 -w1 -c1
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i7 -u3 -r1 -w1 -c1
echo "## fixed (index) insertion with nested rotations"
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i0 -u3 -r2 -w1 -c1
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i0 -u3 -r3 -w1 -c1
run $R/k4_certs_2.json.gz $R/k4_certs_3.json.gz -i0 -u1 -r3 -w1 -c1
echo "## the owner's needs from its base (attempts/lb4-owner-needs-from-base.md)"
for f in 2 3 4_n4_1 4_n4_2 4_n4_3 4_pure; do run $R/k4_certs_$f.json.gz -i2 -u3 -r1 -w0; done
echo "## chains ending at upgraded agents (k4/lb4.md §3, item 2): pure n = 4, m = 8 and 9"
run $R/k4_certs_4_pure.json.gz --m=8 -i2 -u1 -r1 -w1 -c0
run $R/k4_certs_4_pure.json.gz --m=8 -i2 -u3 -r1 -w1 -c0
run $R/k4_certs_4_pure.json.gz --m=9 -i2 -u3 -r1 -w1 -c0
