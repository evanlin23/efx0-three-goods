"""Lemma XD (k4/girth.md section 7): in RF-T's setting with (F1), the official chain "p takes {g, j}, d takes Y_p" at
Y followed by "Y_d to u" gives a partial allocation X_D (p {g, j}, d {Y_p}, u {Y_u, Y_d}, everyone else its Y-pick)
that is EFX0 with only the junk good z left.  At a hard Y, z can then go to NO agent b (else Y would not be an OC1
failure).  On every DEMOTE-0 RF start of the n = 5 exports (RESIDUE.jsonl.gz from k4/girth/oc1_residue_n5.py), for
every valid trade in RF-T's shape with (F1): check that X_D is EFX0 and that the chain is an official move of main's
raw checker (k4/sdc/oc1_mc2_rand.Inst.moves), check that no placement of z completes it, and record what blocks each
placement (who is threatened by which bundle).  EVIDENCE for the facts; the lemma is proved in the text.

    python3 k4/girth/oc1_xd.py RESIDUE.jsonl.gz
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


def key(st):
    return tuple(tuple(sorted(b)) for b in st)


def threats(I, B):
    """(i, k) pairs with i threatened by k's bundle (EFX0, main's definition)"""
    v = I.v
    out = []
    for i in range(I.n):
        own = I.V(i, B[i])
        for k in range(I.n):
            if k != i and B[k] and I.V(i, B[k]) - min(v[i].get(h, 0) for h in B[k]) > own:
                out.append((i, k))
    return out


def main():
    inp = sys.argv[1]
    print('$ python3 k4/girth/oc1_xd.py', os.path.basename(inp), flush=True)
    C = collections.Counter()
    for line in gzip.open(inp, 'rt'):
        r = json.loads(line)
        if r['cls'] != 'DEMOTE-0':
            continue
        S_, V, Y, Y2, u, path = r['sets'], r['vals'], r['Y'], r['Y2'], r['u'], r['path']
        n = len(S_)
        I = Inst(S_, V)
        v = I.v
        rl, J = roles(S_, V, list(Y))
        rl2, J2 = roles(S_, V, list(Y2))
        d = path[-1]
        g = Y2[d]
        if len(path) < 3 or g not in J:
            continue
        found = False
        for p in range(n):
            if rl2[p] != 'Dp' or Y2[p] != Y[p]:
                continue
            for j in sorted(J2):
                if j not in v[p] or j not in J:
                    continue
                if not (I.V(p, [g, j]) > I.V(p, [Y[p]]) and v[d].get(Y[p], 0) > v[d][g]):
                    continue
                rest = [x for x in J2 if x != j]
                if len(rest) != 2 or Y[u] not in rest:
                    continue
                z = [x for x in rest if x != Y[u]][0]
                F1 = v[d].get(Y[p], 0) > v[d][Y[d]]
                C['trades in RF-T\'s shape'] += 1
                C['(F1) holds'] += F1
                if not F1:
                    continue
                found = True
                base = [[x] for x in Y]
                st = [list(b) for b in base]
                st[p] = [g, j]
                st[d] = [Y[p]]
                assert key(st) in {key(s) for s in I.moves(base)}, 'the chain is not official'
                XD = [list(b) for b in st]
                XD[u] = [Y[u], Y[d]]
                ok = I.efx0(XD)
                C['X_D (z unplaced) is EFX0 (must be all)'] += ok
                lab = lambda i: 'd' if i == d else 'u' if i == u else 'p' if i == p else (
                    'x_(l-1)' if i == path[-2] else 'x%d' % path.index(i) if i in path else 'off-path')
                C['u values Y_p: %s; v_u(Y_p) > v_u(Y_u) + v_u(Y_d): %s' % (
                    Y[p] in v[u], v[u].get(Y[p], 0) > v[u][Y[u]] + v[u][Y[d]])] += 1
                anyb = False
                for b in range(n):
                    B = [list(x) for x in XD]
                    B[b].append(z)
                    if I.efx0(B):
                        anyb = True
                        continue
                    th = sorted({(lab(i), lab(k)) for i, k in threats(I, B)})
                    C['z to %s is blocked by (threatened, bundle owner): %s' % (lab(b), th)] += 1
                C['some placement of z completes X_D (must be none at a hard Y)'] += anyb
        C['DEMOTE-0 starts with a trade in RF-T\'s shape and (F1): %s' % found] += 1
    for k in sorted(C):
        print('   %-130s %7d' % (k, C[k]))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
