#!/bin/sh
# The repair-lemma checks of k4/sx.md §4.2 (k4/sx_zprime.py) on the non-completable f = 1 keys of the hunts and the
# n = 3 catalogue, in chunks of 4000 profiles, one process at a time, resumable. Logs: results/k4_sx/zprime/.
O=results/k4_sx/zprime
mkdir -p $O
zp() {  # name dump start
  [ -s $O/$1.log ] && grep -q '^# time' $O/$1.log && return 0
  python3 k4/sx_zprime.py $2 --start=$3 --max=4000 --examples=3 > $O/$1.log 2>&1
}
for f in n3_all_10 n3_all_20 n3_all_30 n3_all_40; do
  n=$(python3 -c "import gzip; print(sum(1 for _ in gzip.open('results/k4_sx/hunt/$f.jsonl.gz', 'rt')))")
  s=0
  while [ $s -lt $n ]; do zp ${f}_s$s results/k4_sx/hunt/$f.jsonl.gz $s; s=$((s + 4000)); done
done
for f in n4_3_r40k n4_pure_r40k n5_pure_r1000_3000 n5_pure_r1000_4000 n4_3_r400k n4_pure_r400k n5_pure_r10k_0 n5_pure_r10k_1000 n5_pure_r10k_2000 n5_pure_r10k_3000 n5_pure_r10k_4000; do
  [ -f results/k4_sx/hunt/$f.jsonl.gz ] && grep -q '^distinct' results/k4_sx/hunt/$f.log && zp $f results/k4_sx/hunt/$f.jsonl.gz 0
done
