"""The 32 DEMOTE-0 starts at n = 5 that need the 3-ring (T*) (k4/girth.md section 7): an explicit certificate.
For each, some official 3-ring "c1 takes {Y'_d, j}, c2 takes Y'_c1, d takes Y'_c2" (c1 pick-dangerous at Y', everyone
improves) after which d absorbs ALL the remaining junk and every other agent keeps its bundle is EFX0 (raw,
k4/sdc/oc1_mc2_rand.Inst.efx0; the ring is checked to be in Inst.moves).  Plus the roles of u, d, c1, c2.

    python3 k4/girth/oc1_tstar.py RESIDUE.jsonl.gz
"""
import collections
import gzip
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
from oc1_residue import key  # noqa: E402


def main():
    print('$ python3 k4/girth/oc1_tstar.py', os.path.basename(sys.argv[1]), flush=True)
    C = collections.Counter()
    for line in gzip.open(sys.argv[1], 'rt'):
        r = json.loads(line)
        if r['cls'] != 'DEMOTE-0':
            continue
        S, V, Y, Y2, u, path = r['sets'], r['vals'], tuple(r['Y']), tuple(r['Y2']), r['u'], r['path']
        n = len(S)
        I = Inst(S, V)
        v = I.v
        d = path[-1]
        w = path[1] if len(path) > 1 else d
        rl, J = roles(S, V, list(Y))
        rl2, J2 = roles(S, V, list(Y2))
        J2 = sorted(J2)
        base = [[p] for p in Y2]
        if len(J2) >= 2 and (owner_ok(I, base, w) or owner_ok(I, base, d)):
            continue
        trade = any(I.V(p, [Y2[d], j]) > I.V(p, [Y2[p]]) and I.V(d, [Y2[p]]) > I.V(d, [Y2[d]])
                    for p in range(n) if rl2[p] == 'Dp' for j in J2 if j in v[p])
        if trade:
            continue
        C['DEMOTE-0 starts with no w/d owner and no trade (the 3-ring starts)'] += 1
        C['hypergraph ' + r['h']] += 1
        ok = False
        official = {key(s) for s in I.moves(base)}
        for c1 in range(n):
            if c1 == d or rl2[c1] != 'Dp':
                continue
            for c2 in range(n):
                if c2 in (d, c1):
                    continue
                for j in J2:
                    if j not in v[c1]:
                        continue
                    if not (I.V(c1, [Y2[d], j]) > I.V(c1, [Y2[c1]]) and I.V(c2, [Y2[c1]]) > I.V(c2, [Y2[c2]])
                            and I.V(d, [Y2[c2]]) > I.V(d, [Y2[d]])):
                        continue
                    st = [list(b) for b in base]
                    st[c1] = [Y2[d], j]
                    st[c2] = [Y2[c1]]
                    st[d] = [Y2[c2]]
                    assert key(st) in official
                    X = [list(b) for b in st]
                    X[d] += [g for g in J2 if g != j]
                    if I.efx0(X):
                        ok = True
                        C['roles at Y: u %s, d %s, c1 %s, c2 %s; c2 keeps its pick %s' % (
                            rl[u], rl[d], rl[c1], rl[c2], Y2[c2] == Y[c2])] += 1
                        break
                if ok:
                    break
            if ok:
                break
        C['a 3-ring, then d absorbs all remaining junk: EFX0'] += ok
    for k in sorted(C):
        print('   %-80s %5d' % (k, C[k]))


if __name__ == '__main__':
    main()
