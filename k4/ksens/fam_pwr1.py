"""PW variants against R1-priority orders (k4/ksens.md §4): PW(f, W, r) with clean values, where in addition the
wanters value the pool goods they list in WD (pool indices) slightly above their own good q (value 1.5 -> scaled), so
that a frozen agent displaced onto that pool good under R1 is itself wanted and offers no slot.  Reports, over every
R1-priority start, how many fail OC1 (and OC).

    python3 k4/ksens/fam_pwr1.py f W r WD   (WD: comma-separated pool indices, e.g. 0 or 0,1; '-' for none)"""
import sys, itertools, json
import _paths
import ocsat
from r1_pw import sd_r1


def make(f, W, r, WD):
    P = list(range(f)); Q = list(range(f, f + W)); D = list(range(f + W, f + W + r))
    sets = [[j] + D for j in range(f)]; vals = [[40] + [38 - 2 * t for t in range(r)] for j in range(f)]
    for i in range(W):
        sets.append(P + [Q[i]] + [D[t] for t in WD]); vals.append([4 * (f - j) for j in range(f)] + [2] + [3] * len(WD))
    return sets, vals, f + W + r


if __name__ == '__main__':
    f, W, r = map(int, sys.argv[1:4]); WD = [] if sys.argv[4] == '-' else [int(x) for x in sys.argv[4].split(',')]
    sets, vals, m = make(f, W, r, WD); n = f + W
    O = ocsat.OC(sets, vals, m); st = {}
    for o in itertools.permutations(range(n)): st.setdefault(tuple(sd_r1(sets, vals, o, m)), o)
    bad1 = [Y for Y in st if not O.holds(ocsat.bases_of(Y, n), chain='any', A=1)]
    bad = [Y for Y in bad1 if not O.holds(ocsat.bases_of(Y, n), chain='any')]
    print('PWR1 f %d W %d r %d WD %s: k %d n %d m %d; R1 starts %d; OC1 fails on %d, OC on %d %s' % (f, W, r, WD,
          max(map(len, sets)), n, m, len(st), len(bad1), len(bad), ('e.g. picks %s order %s %s' % (bad1[0], st[bad1[0]], json.dumps((sets, vals)))) if bad1 else ''), flush=True)
