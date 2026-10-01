#!/usr/bin/env python3
"""Second implementation for the DL_R runs (k4/dl2.md §3): main's k4/c4x_check.py enumerates 𝒫 and its deficit
`rodef` on its own (every base map good -> agent or junk, (V1), (V2) literally), and the relation memberships below are
written separately from k4/dl2_relations.py. For sampled profiles, compares per def > 0 state: the deficit, the nearest
distance k, and whether DL_R holds, for R in REL_B (R2, RB2, RSY+2, RT).
usage: python3 k4/dl2_relations_xcheck.py suite | catalog FILE [--every=E] [--max=N]"""
import gzip, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import c4x_check as CX
import dl2_relations as DR


def rel_B(name, sets, vals, P, P2):
    """membership of the move P -> P2 (tuples of frozensets) in relation `name`"""
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    val = lambda i, B: sum(vl[i].get(g, 0) for g in B)
    nd = lambda i, B: frozenset(g for g in vl[i] if g not in B and vl[i][g] > val(i, B))
    N1 = [nd(i, P[i]) for i in range(len(P))]; N2 = [nd(i, P2[i]) for i in range(len(P))]
    NA1 = frozenset().union(*N1); NA2 = frozenset().union(*N2)
    fz1 = [len(B) == 1 and B <= NA1 for B in P]; fz2 = [len(B) == 1 and B <= NA2 for B in P2]
    ch = [i for i in range(len(P)) if P[i] != P2[i]]
    if name == 'R2': return len(ch) <= 2
    if len(ch) == 1: return NA1 == NA2 or name != 'RT'
    trade = len(ch) == 2 and NA1 == NA2 and not any(fz1[i] or fz2[i] for i in ch)
    xs = [i for i in ch if fz1[i] and not fz2[i]]; zs = [i for i in ch if fz2[i] and not fz1[i]]
    ws = [i for i in ch if fz1[i] and fz2[i]]; ys = [i for i in ch if not fz1[i] and not fz2[i]]
    swap = (len(xs) == 1 and len(zs) == 1 and not ws and NA1 == NA2 and P2[zs[0]] == P[xs[0]]
            and P[xs[0]] <= N1[zs[0]])
    if name == 'RB2': return trade or (swap and not ys)
    if name == 'RSY+2': return trade or (swap and len(ys) <= 1)
    if name == 'RT':
        exch = trade and bool(P2[ch[0]] & P[ch[1]] or P2[ch[1]] & P[ch[0]])
        return exch or (swap and len(ys) <= 1 and all(P[y] - P2[y] for y in ys))
    raise ValueError(name)


REL_B = ('R2', 'RB2', 'RSY+2', 'RT')


def states_B(sets, vals, m):
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    res = CX.analyse(sets, m, vl)
    mf = max(r[2]['-frozen'] for r in res)
    mp = [(tuple(r[0]), r[2]['rodef']) for r in res if r[2]['-frozen'] == mf]
    out = {}
    for P, d in mp:
        if d <= 0: continue
        better = [P2 for P2, d2 in mp if d2 < d]
        k = min((sum(1 for a, b in zip(P, P2) if a != b) for P2 in better), default=None)
        out[tuple(tuple(sorted(B)) for B in P)] = (d, k, {r: any(rel_B(r, sets, vals, P, P2) for P2 in better)
                                                          for r in REL_B})
    return out


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv[1:] if a.startswith('--'))
    rest = [a for a in argv[1:] if not a.startswith('--')]
    items = DR.items_of(argv[0], rest, opt)
    if 'max' in opt and argv[0] == 'suite': items = items[:int(opt['max'])]
    print('# command: python3 k4/dl2_relations_xcheck.py ' + ' '.join(argv), flush=True)
    nprof = nst = bad = 0
    for d, src in items:
        if len(d['sets']) > 4: continue                   # c4x_check enumerates base maps: n <= 4 only
        A = {tuple(tuple(b) for b in r['Bs']): r for r in DR.profile(d)}
        B = states_B(d['sets'], d['vals'], d['m'])
        nprof += 1
        if set(A) != set(B):
            bad += 1; print('MISMATCH states', src, sorted(set(A) ^ set(B))[:3], flush=True); continue
        for P, (dB, kB, hB) in B.items():
            nst += 1
            a = A[P]
            if a['def'] != dB or a['k'] != kB or any(a['holds'][r] != hB[r] for r in REL_B):
                bad += 1
                print('MISMATCH', src, P, 'A', a['def'], a['k'], {r: a['holds'][r] for r in REL_B}, 'B', dB, kB, hB,
                      flush=True)
    print('profiles %d (n <= 4), def>0 states %d, mismatches %d (deficit, nearest distance, DL_R for %s)' % (
        nprof, nst, bad, ', '.join(REL_B)), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
