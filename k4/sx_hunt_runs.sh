#!/bin/sh
# Hunts for non-completable f = 1 keys with k4/red.c (k4/sx_hunt.py), one process at a time, resumable per piece.
# Output: results/k4_sx/hunt/<name>.{log,jsonl.gz}.
O=results/k4_sx/hunt
mkdir -p $O
hunt() {  # name file rand seed cores
  [ -s $O/$1.log ] && grep -q '^distinct' $O/$1.log && return 0
  python3 k4/sx_hunt.py $2 --rand=$3 --seed=$4 --cores=$5 --out=$O/$1.jsonl.gz > $O/$1.log 2>&1
}
hunt n4_3_r40k results/k4_certs_4_n4_3.json.gz 40000 7 0:400
hunt n4_pure_r40k results/k4_certs_4_pure.json.gz 40000 7 0:300
hunt n4_2_r20k results/k4_certs_4_n4_2.json.gz 20000 7 0:400
for a in 0 1000 2000 3000 4000; do
  hunt n5_pure_r1000_$a results/k4_certs_5_pure.json.gz 1000 11 $a:$((a + 1000))
done
for a in 0 2000 4000 6000 8000; do
  hunt n5_n4_4_r200_$a results/k4_certs_5_n4_4.json.gz 200 11 $a:$((a + 2000))
  hunt n5_n4_3_r200_$a results/k4_certs_5_n4_3.json.gz 200 11 $a:$((a + 2000))
done
hunt n5_n4_2_r200 results/k4_certs_5_n4_2.json.gz 200 11 0:6000
