"""Towards (LIFT-1) (k4/matching.md §6): who threatens the owner's bundle in the LIFT shape (evidence only).

For every start of results/k4_matching/data/oc1max_cex_n4.json and results/k4_matching/n4_failing_walk.jsonl, take
the LIFT pairs that meet Lemma LIFT-red's hypotheses (z unfrozen after P1, |H0 of P1| = 2, P2 canonical ending at z
with z's favourite good, h not P1's head) and satisfy Lemma EX* at B2 with owner h.  For each, with X = H0 of P2 plus
all the junk of B2 (H = empty): the agents X threatens at their B2 values, by role (z, P1's head k, the second
sharer, other), and how many of their relevant goods X holds; when X threatens somebody, the kept-out goods of the
least H that works and who receives them.

    python3 k4/matching/lift1_threats.py"""
import sys, os, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, subsets, bip_match
from lift_shapes import chain_moves
from exchange import ex_value_general


def least_H(I, B2, o):
    """Least kept-out set H (Lemma M at B2, owner o) and an assignment of H to holders; None if none."""
    J2 = I.junk(B2); bv = [I.V(i, B2[i]) for i in range(I.n)]; hold = [u for u in I.holders(B2) if u != o]
    nonh = [q for q in range(I.n) if q != o and q not in hold]
    for H in subsets(J2):
        X = list(B2[o]) + [g for g in J2 if g not in H]
        if any(I.threat(q, X, bv[q]) for q in nonh): continue
        E = [u for u in hold if I.threat(u, X, bv[u])]
        adj = {h: [u for u in hold if u not in E or (I.v[u].get(h, 0) > 0 and not I.threat(u, X, bv[u] + I.v[u][h]))]
               for h in H}
        m = bip_match(H, adj)
        if len(m) == len(H) and all(u in m for u in E): return H, {g: u for u, g in m.items()}, E
    return None


def job(row):
    I = M(row['sets'], row['vals']); Y = row['picks']; base = [[g] for g in Y]
    D = I.dangerous(base); z = I.holders(base)[0]; C = collections.Counter(); best = None
    for P1, H01, Hs1, B1 in chain_moves(I, base, D):
        if P1[-1] != z or len(H01) != 2 or z in I.frozen(B1): continue
        if any(Hs1.get(i) for i in range(1, len(P1))): continue   # no junk for P1's agents after its head
        sharers = [q for q in D if q != P1[0] and I.V(q, [g for g in H01 if g in I.R[q]]) > I.V(q, base[q])]
        if not sharers: continue
        for P2, H02, Hs2, B2 in chain_moves(I, B1):
            h = P2[0]
            if P2[-1] != z or h == P1[0] or any(Hs2.get(i) for i in range(1, len(P2))): continue
            if len(B2[z]) != 1 or I.V(z, B2[z]) < max(I.v[z].values()): continue
            if ex_value_general(I, B1, P2, B2, h)[0] > 0: continue
            X = list(B2[h]) + I.junk(B2)
            thr = [i for i in range(I.n) if i != h and I.threat(i, X, I.V(i, B2[i]))]
            key = (len(thr), len(P2))
            if best is None or key < best[0]: best = (key, P1, P2, B2, h, X, thr, sharers)
    if best is None: C['no LIFT-red pair'] += 1; return C
    _, P1, P2, B2, h, X, thr, sharers = best
    role = lambda i: 'z' if i == z else 'k (P1 head)' if i == P1[0] else 'sharer' if i in sharers else \
        'on P2' if i in P2 else 'other'
    C['LIFT-red pairs exist'] += 1
    C['H = empty works: %s' % (not thr)] += 1
    for i in range(I.n):
        if i == h: continue
        C['role %s: goods of X it values = %d' % (role(i), len(set(X) & I.R[i]))] += 1
    for i in thr:
        C['threatened by X (H = empty): %s' % role(i)] += 1
    if thr:
        r = least_H(I, B2, h)
        if r is None: C['no H at all (EX* used another witness)'] += 1
        else:
            H, asg, E = r
            C['least H size %d' % len(H)] += 1
            for g, u in asg.items(): C['kept-out good goes to %s' % role(u)] += 1
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
    print('$ python3 k4/matching/lift1_threats.py |', len(rows), 'starts', flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C in pool.imap_unordered(job, rows, chunksize=8): T.update(C)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
