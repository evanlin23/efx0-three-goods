#!/bin/bash
# Writes results/k4_c4_chain.log (k4/c4.md §7): the explicit allocations of H_t (t <= 8), then LB4r with index
# insertion on H_t with one rotation fewer than Proposition H's bound ceil(2t/3) (it fails) and with the bound (it
# succeeds). t <= 3 with LB4r's own options (-w1: the owner's needs from its bundle, which enumerates every larger set C,
# 2^|J| per owner); t = 4 with the owner's needs from its base (-w0), since -w1 at t = 4 (|J| = 26) is out of reach.
cd "$(dirname "$0")/.."
L=results/k4_c4_chain.log
python3 k4/c4_chain.py check 1,2,3,4,5,6,8 > $L 2>&1
for t in 1 2 3; do
    q=$(( (2 * t + 2) / 3 )); p=$(( q - 1 ))
    python3 k4/c4_chain.py run $t "-i0 -u3 -r$p -w1 -c1" "-i0 -u3 -r$q -w1 -c1" >> $L 2>&1
done
python3 k4/c4_chain.py run 4 "-i0 -u3 -r2 -w0 -c1" "-i0 -u3 -r3 -w0 -c1" >> $L 2>&1
