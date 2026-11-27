"""DEMOTE-0's trade case at n = 5 (k4/girth.md section 7): canonical forms.  For every DEMOTE-0 RF start of the full
n = 5 exports (built by k4/girth/oc1_residue_n5.py) that has no completion owned by w or d, every valid trade
(p pick-dangerous at Y': p takes {Y'_d, j}, d takes Y'_p, both improve) and fixed rules for placing the remaining junk
goods one per agent (raw EFX0, k4/sdc/oc1_mc2_rand.Inst.efx0).  Reports which (trade rule, placement rule) pairs work
at every start, and the facts that a proof would use.

    python3 k4/girth/oc1_trade.py RESIDUE.jsonl.gz [STRIDE]
"""
import collections
import gzip
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_rf_owner import owner_ok  # noqa: E402


def main():
    inp = sys.argv[1]
    stride = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    print('$ python3 k4/girth/oc1_trade.py', os.path.basename(inp), stride, flush=True)
    C = collections.Counter()
    k = 0
    for line in gzip.open(inp, 'rt'):
        r = json.loads(line)
        if r['cls'] != 'DEMOTE-0':
            continue
        k += 1
        if k % stride:
            continue
        S_, V, Y, Y2, u, path = r['sets'], r['vals'], tuple(r['Y']), tuple(r['Y2']), r['u'], r['path']
        n = len(S_)
        I = Inst(S_, V)
        v = I.v
        rl, J = roles(S_, V, list(Y))
        rl2, J2 = roles(S_, V, list(Y2))
        J2 = sorted(J2)
        d = path[-1]
        w = path[1] if len(path) > 1 else d
        base = [[p] for p in Y2]
        if len(J2) >= 2 and (owner_ok(I, base, w) or owner_ok(I, base, d)):
            continue
        trades = []
        for p in range(n):
            if rl2[p] != 'Dp':
                continue
            for j in J2:
                if j in v[p] and I.V(p, [Y2[d], j]) > I.V(p, [Y2[p]]) and I.V(d, [Y2[p]]) > I.V(d, [Y2[d]]):
                    trades.append((p, j))
        if not trades:
            continue
        C['trade starts'] += 1
        C['path length %d' % (len(path) - 1)] += 1
        C['path length %d: remaining junk goods after the trade: %d' % (len(path) - 1, len(J2) - 1)] += 1
        C['valid trades %d' % min(len(trades), 5)] += 1
        # facts
        C['every valid p is truly dangerous at Y'] += all(rl[p] == 'DT' for p, j in trades)
        C['every valid p holds its own pick at Y\''] += all(Y2[p] == Y[p] for p, j in trades)
        C['every valid j is junk at Y'] += all(j in J for p, j in trades)
        C["d's new good Y'_d is junk at Y"] += Y2[d] in J
        C["u's old pick Y_u is junk at Y'"] += Y[u] in J2

        def place_ok(p, j, rule):
            st = [list(b) for b in base]
            st[p] = [Y2[d], j]
            st[d] = [Y2[p]]
            rest = [g for g in J2 if g != j]
            if rule == 'singles: any':
                for recv in itertools.permutations(range(n), len(rest)):
                    B = [list(b) for b in st]
                    for g, i in zip(rest, recv):
                        B[i].append(g)
                    if I.efx0(B):
                        return True
                return False
            B = [list(b) for b in st]
            if rule == 'Y_u to d, other junk to w':
                if w == d or len(rest) > 2:
                    return False
                for g in rest:
                    B[d if g == Y[u] else w].append(g)
            elif rule == 'Y_u to w, other junk to d':
                if w == d or len(rest) > 2:
                    return False
                for g in rest:
                    B[w if g == Y[u] else d].append(g)
            elif rule in ('Y_u to d, other junk to x2', 'Y_u to x2, other junk to d'):
                if len(path) != 4 or len(rest) > 2:
                    return False
                x2 = path[2]
                for g in rest:
                    if rule == 'Y_u to d, other junk to x2':
                        B[d if g == Y[u] else x2].append(g)
                    else:
                        B[x2 if g == Y[u] else d].append(g)
            elif rule == 'all remaining junk to d':
                B[d] += rest
            elif rule == 'all remaining junk to w':
                B[w] += rest
            return I.efx0(B)

        # Lemma RF-T's reduction: the canonical allocation X (p: {Y'_d, j}; d: {Y_p, Y_u}; x_{l-1}: {Y_d, z}; u: t;
        # everyone else its Y' pick) is EFX0 iff (W-d) nobody but x_{l-1} wants Y_d at X and (W-p) nobody but d
        # wants Y_p at X ("wants" = values that single good above its own bundle)
        xl1 = path[-2]
        for p, j in trades:
            rest = [g for g in J2 if g != j]
            if len(rest) != 2 or Y[u] not in rest:
                C['RF-T: remaining junk is not {Y_u, z}'] += 1
                continue
            z = [g for g in rest if g != Y[u]][0]
            X = [[g] for g in Y2]
            X[p] = [Y2[d], j]
            X[d] = [Y2[p], Y[u]]
            X[xl1] = [Y2[xl1], z]
            assert Y2[xl1] == Y[d]
            ef = I.efx0(X)
            val = [I.V(i, X[i]) for i in range(n)]
            wd = all(v[i].get(Y[d], 0) <= val[i] for i in range(n) if i != xl1)
            wp = all(v[i].get(Y[p], 0) <= val[i] for i in range(n) if i != d)
            C['RF-T: X EFX0 == ((W-d) and (W-p))'] += ef == (wd and wp)
            C['RF-T: X EFX0'] += ef
            C['RF-T: (W-d) holds'] += wd
            C['RF-T: (W-p) holds'] += wp
            C['RF-T: trades tested'] += 1
        rules = ['singles: any', 'Y_u to d, other junk to w', 'Y_u to w, other junk to d', 'all remaining junk to d',
                 'all remaining junk to w', 'Y_u to d, other junk to x2', 'Y_u to x2, other junk to d']
        for rule in rules:
            C['some valid trade + %s' % rule] += any(place_ok(p, j, rule) for p, j in trades)
            C['every valid trade + %s' % rule] += all(place_ok(p, j, rule) for p, j in trades)
    for kk in sorted(C):
        print('   %-70s %7d' % (kk, C[kk]))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
