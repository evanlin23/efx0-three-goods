"""Lemma LIFT-1 (k4/matching.md §6): its hypotheses (L1)-(L3) on the data, and its construction against raw EFX0.

For every start of results/k4_matching/data/oc1max_cex_n4.json and results/k4_matching/n4_failing_walk.jsonl, over the
LIFT pairs meeting Lemma LIFT-red's hypotheses (z unfrozen after P1; |H0 of P1| = 2 inside J + {y_z}; no junk for
P1's agents after its head; P2 canonical
ending at z with z's favourite good; h not P1's head):
  (L1) z is unfrozen at B2;
  (L2) v_z(H0 of P2, restricted to R_z) <= v_z(favourite good);  with L2WEAK=1 (default) the weaker
  (L2') v_z(H0 of P2, restricted to R_z) <= v_z(favourite good) + v_z(g), g z's most valuable good of J2 (0 if none);
  (L3) every agent other than h and z values at most one good of X = (H0 of P2) + J2.
The lemma's allocation (h gets X minus g, z gets its favourite good plus g, its most valuable good of J2 if it values
any, everybody else keeps B2) is built and checked with raw EFX0 whenever (L1)-(L3) hold.  Also recorded: which of
(L1)-(L3) fails when no pair meets all three, and whether the sharer's (L3) ever fails (Lemma PL(c) says no).

    python3 k4/matching/lift1_check.py"""
import sys, os, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from lift_shapes import chain_moves
WEAK = os.environ.get('L2WEAK', '1') == '1'   # use (L2') (default) instead of (L2)


def job(row):
    I = M(row['sets'], row['vals']); Y = row['picks']; base = [[g] for g in Y]; J = I.junk(base)
    D = I.dangerous(base); z = I.holders(base)[0]; C = collections.Counter(); found = False; fails = collections.Counter()
    for P1, H01, Hs1, B1 in chain_moves(I, base, D):
        if P1[-1] != z or len(H01) != 2 or z in I.frozen(B1) or not set(H01) <= set(J) | {Y[z]}: continue
        if any(Hs1.get(i) for i in range(1, len(P1))): continue   # no junk for P1's agents after its head
        sharers = [q for q in D if q != P1[0] and I.V(q, [g for g in H01 if g in I.R[q]]) > I.V(q, base[q])]
        if not sharers: continue
        for P2, H02, Hs2, B2 in chain_moves(I, B1):
            h = P2[0]
            if P2[-1] != z or h == P1[0] or any(Hs2.get(i) for i in range(1, len(P2))): continue
            if len(B2[z]) != 1: continue
            t = B2[z][0]
            if I.v[z][t] < max(I.v[z].values()): continue
            J2 = I.junk(B2); X = list(B2[h]) + J2
            L1 = z not in I.frozen(B2)
            Gz = [g for g in J2 if g in I.R[z]]; gbest = max([I.v[z][g] for g in Gz] + [0])
            L2 = I.V(z, [g for g in B2[h] if g in I.R[z]]) <= I.v[z][t]
            L2p = I.V(z, [g for g in B2[h] if g in I.R[z]]) <= I.v[z][t] + gbest   # (L2'): z's best junk good helps
            if L2p and not L2: C["(L2') holds where (L2) fails"] += 1
            L2 = L2p if WEAK else L2
            L3 = all(len(set(X) & I.R[i]) <= 1 for i in range(I.n) if i not in (h, z))
            for q in sharers:
                if q != h and q not in P2 and len(set(X) & I.R[q]) > 1: C['sharer off P2 values >= 2 goods of X (PL(c) violated?!)'] += 1
            if L1 and L2 and L3:
                found = True
                G = [g for g in J2 if g in I.R[z]]
                A = [list(b) for b in B2]
                if G:
                    g = max(G, key=lambda x: I.v[z][x]); A[h] = [x for x in X if x != g]; A[z] = [t, g]
                else:
                    A[h] = X
                ok = I.efx0(A) and sorted(x for b in A for x in b) == list(range(I.m))
                C['LIFT-1 construction raw EFX0 %s' % ok] += 1
                if not ok: C['LIFT-1 COUNTEREXAMPLE'] += 1; print('LIFT-1 FAILS', json.dumps(row), P1, H01, P2, H02, A, flush=True)
            else:
                fails[('L1' if not L1 else '') + ('L2' if not L2 else '') + ('L3' if not L3 else '')] += 1
    C['some LIFT-red pair meets (L1)-(L3): %s' % found] += 1
    if not found:
        for k in fails: C['  (when none does) a pair fails exactly %s' % k] += 1
    return C


if __name__ == '__main__':
    R = os.path.join(_mpaths.ROOT, 'results', 'k4_matching')
    rows = [dict(sets=d['sets'], vals=d['vals'], picks=d['picks'])
            for d in json.load(open(os.path.join(R, 'data', 'oc1max_cex_n4.json')))['instances']]
    rows += [json.loads(l) for l in open(os.path.join(R, 'n4_failing_walk.jsonl'))]
    _seen = set(); _rows = []   # distinct (sets, vals, picks): the 11 stored are also in the walk dump
    for _r in rows:
        _k = json.dumps([_r['sets'], _r['vals'], list(_r['picks'])])
        if _k not in _seen: _seen.add(_k); _rows.append(_r)
    rows = _rows
    print('$ python3 k4/matching/lift1_check.py |', len(rows), 'starts', flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C in pool.imap_unordered(job, rows, chunksize=8): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
