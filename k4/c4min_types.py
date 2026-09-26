#!/usr/bin/env python3
"""Order types of the agents in the tightest profiles found by the climber (k4/c4min_hunt.md §3).

A strict balanced 4-good type with values a > b > c > d is classified by
  pos: where a lies among the pair sums c+d < b+d < b+c (0: a < c+d, 'flat'; 1; 2; 3: a > b+c),
  b vs c+d, and a+d vs b+c;
a 3-good type by nothing (all six are alike up to the ranking). Reads climber dumps (JSON lines with a 'line' field,
k4/c4min_climb.py --dump) and prints, for the profiles with an owner needed and d* = 0 (and, separately, all dumped
profiles), the frequency of each 4-good class, against the frequency of the class among the 288 strict balanced types.

usage: c4min_types.py DUMP.jsonl [DUMP.jsonl ...]"""
import json, sys
from collections import Counter
from c4min_climb import parse_profile
from check4 import strict_balanced_types
from c4min_common import type_class, CLASSES


def cls(v):
    k = type_class(v)
    pos, bcd, adbc = CLASSES[k]
    return (k, pos, 'b>c+d' if bcd else 'b<c+d', 'a+d>b+c' if adbc else 'a+d<b+c')


def main():
    base = Counter(cls(v) for v in strict_balanced_types(4))
    tight, allp = Counter(), Counter()
    nt = na = 0
    for f in sys.argv[1:]:
        for l in open(f):
            r = json.loads(l)
            vals = parse_profile(r['line'], None)
            cs = [cls(list(v.values())) for v in vals if len(v) == 4]
            allp.update(cs); na += 1
            if r['owner'] and r['dstar'] == 0: tight.update(cs); nt += 1
    print(f'profiles: {na} dumped, {nt} with an owner needed and d* = 0')
    print('class (index, pos of a among c+d<b+d<b+c, b vs c+d, a+d vs b+c): share among the 288 types / all dumped / tight')
    for k in sorted(base):
        sb = base[k] / sum(base.values())
        sa = allp[k] / max(1, sum(allp.values()))
        st = tight[k] / max(1, sum(tight.values()))
        print(f'  {k}: {sb:.3f} / {sa:.3f} / {st:.3f}')


if __name__ == '__main__':
    main()
