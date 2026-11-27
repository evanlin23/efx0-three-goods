"""Shapes of the two-move repairs (first chain P1, then a Lemma EX* exchange P2) at starts with no one-move repair
(k4/matching.md §6; evidence only).  Data: the 11 stored n = 4 OC1^max failures, the failing profile-start pairs
of the value walks (results/k4_matching/n4_failing_walk.jsonl, from n4_walk.py with DUMP), the TTC session's n = 5
strict-core failure (k4/oc1_hall.md §22), and RD5, PW5 (k = 5).

For every start, over every official chain P1 from a dangerous agent and every official chain P2 at the state B1
after it with an owner o satisfying EX* (exchange.ex_value_general), record the features of the recipe
    LIFT: P1 ends at the lone holder z of Y, and its H0 (inside J + B_z) is also improving for a second dangerous
          agent (a shared danger set, k4/oc1_hall.md §23.3); P2 ends at z, and after P2 z holds its favourite good of R_z (it wants nothing), so every
          agent frozen only by z is unfrozen; the owner is P2's head.
and count the starts where some repairing pair has each feature.

    python3 k4/matching/lift_shapes.py [MAX_ROWS]"""
import sys, os, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, subsets
from exchange import all_chains, apply_chain, ex_value_general


def chain_moves(I, base, starts=None):
    J = I.junk(base)
    for P, Hs in all_chains(I, base, starts):
        k, xt = P[0], P[-1]; used = set(g for h in Hs.values() for g in h)
        pool = [g for g in J if g not in used] + list(base[xt])
        for H0 in subsets([g for g in pool if g in I.R[k]], 1):
            if I.V(k, H0) > I.V(k, base[k]):
                yield P, list(H0), Hs, apply_chain(I, base, P, list(H0), Hs)


def job(row):
    I = M(row['sets'], row['vals']); Y = row['picks']; base = [[g] for g in Y]
    D = I.dangerous(base); hold = I.holders(base); J = I.junk(base)
    F = collections.Counter(); F['holders at Y = %d' % len(hold)] += 1
    z = hold[0] if len(hold) == 1 else None
    feats = collections.defaultdict(bool)
    for P1, H01, Hs1, B1 in chain_moves(I, base, D):
        # shared danger set (k4/oc1_hall.md §23.3): H0 of P1 is also improving for a second dangerous agent q,
        # inside J + B_z (z = P1's end); H0 may contain z's released pick
        shared = any(q != P1[0] and I.V(q, [g for g in H01 if g in I.R[q]]) > I.V(q, base[q]) for q in D)
        dem = [q for q in I.frozen(B1) if q in D and q != P1[0]]
        for P2, H02, Hs2, B2 in chain_moves(I, B1):
            for o in range(I.n):
                d, _, _ = ex_value_general(I, B1, P2, B2, o)
                if d > 0: continue
                feats['repair'] = True
                a = P1[-1] == z; b = shared; c = P2[-1] == z
                top = z is not None and B2[z] and I.V(z, B2[z]) >= max(I.v[z].values())
                unfrz = all(q not in I.frozen(B2) or q == P2[0] for q in dem)
                feats['P1 ends at the lone holder z'] |= a
                feats['P1 head takes a shared danger set'] |= b
                feats['P2 ends at z'] |= c
                feats['P2 gives z its favourite good'] |= top
                feats['P2 removes every DEMAND agent of P1 (starts at it or unfreezes it)'] |= unfrz
                feats['owner = P2 head'] |= (o == P2[0])
                feats['owner = z'] |= (o == z)
                feats['LIFT recipe (all of the above but owner = z)'] |= (a and b and c and top and unfrz and o == P2[0])
                feats['P1 at z with shared set; P2 removes DEMAND'] |= (a and b and unfrz)
                feats['P2 has length 1'] |= (len(P2) == 2)
                feats['P2 head is in D'] |= (P2[0] in D)
    for k, v in feats.items(): F[k + ': ' + str(v)] += 1
    for k in ('P1 ends at the lone holder z', 'P1 head takes a shared danger set', 'P2 ends at z',
              'P2 gives z its favourite good', 'P2 removes every DEMAND agent of P1 (starts at it or unfreezes it)',
              'LIFT recipe (all of the above but owner = z)', 'P1 at z with shared set; P2 removes DEMAND'):
        if k not in feats: F[k + ': False'] += 1
    return row, F, feats['LIFT recipe (all of the above but owner = z)']


if __name__ == '__main__':
    R = os.path.join(_mpaths.ROOT, 'results', 'k4_matching')
    rows = [dict(sets=d['sets'], vals=d['vals'], picks=d['picks'], name='cex%d' % t)
            for t, d in enumerate(json.load(open(os.path.join(R, 'data', 'oc1max_cex_n4.json')))['instances'])]
    rows += [dict(json.loads(l), name='walk%d' % t) for t, l in enumerate(open(os.path.join(R, 'n4_failing_walk.jsonl')))]
    _seen = set(); _rows = []   # distinct (sets, vals, picks): the 11 stored are also in the walk dump
    for _r in rows:
        _k = json.dumps([_r['sets'], _r['vals'], list(_r['picks'])])
        if _k not in _seen: _seen.add(_k); _rows.append(_r)
    rows = _rows
    I5 = M([[0,4,5,6],[2,3,4,6],[0,1,5,6],[2,4,5,6],[0,1,7,8]], [[3,2,10,6],[4,1,6,8],[2,8,5,4],[5,4,8,2],[7,8,2,4]])
    rows.append(dict(sets=I5.sets, vals=I5.vals, picks=list(I5.sd((1, 3, 4, 2, 0))), name='TTC-n5'))   # k4/oc1_hall.md §22
    from cex_deficiency import PW5, RD5
    rows += [dict(sets=RD5[0], vals=RD5[1], picks=[1, 3, 4, 2], name='RD5 (k = 5)'),
             dict(sets=PW5[0], vals=PW5[1], picks=[0, 1, 2, 3, 4], name='PW5 (k = 5)')]
    if len(sys.argv) > 1: rows = rows[:int(sys.argv[1])]
    print('$ python3 k4/matching/lift_shapes.py', *sys.argv[1:], '|', len(rows), 'starts', flush=True)
    T = collections.Counter(); t0 = time.time(); miss = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for row, F, ok in pool.imap_unordered(job, rows, chunksize=8):
            T.update(F)
            if not ok: miss.append(row)
    for k in sorted(T): print(k, T[k])
    for r in miss[:8]: print('LIFT recipe misses', r['name'], json.dumps([r['sets'], r['vals']]), 'picks', r['picks'])
    print('time %.0f s' % (time.time() - t0))
