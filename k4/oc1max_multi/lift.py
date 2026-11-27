"""The second move (Sub-lemma OC2-LIFT, k4/oc1_hall.md §23.3; k4/oc1max_multi.md §8): at OC1 failures (perfect starts
with no one-absorber completion at the picks or after one official move), every repairing pair of official moves
(P1, P2) (raw enumeration, mmlib: one-absorber completion after P2), classified.

For P1 a canonical chain from k in D with an improving H_0 (mmlib.is_canonical), its DEMAND agents are the q in
D - {k} frozen after P1 and threatened by the pool (dred.obstacles).  For P2 (a move at B1):
  LIFT     : every DEMAND agent of P1 starts P2 or is unfrozen after P2 (OC2-LIFT's condition 1);
  P2-can   : P2 is a canonical chain at B1 (every x_i wants B1_{x_{i-1}} alone, head unfrozen at B1);
  P2-head=z: P2's head is P1's head z;
  P2-from  : who starts P2: a DEMAND agent of P1, another dangerous agent of the picks, a frozen non-dangerous agent,
             an unfrozen agent, or k.
Per start, the existence of a repairing pair of each kind is counted; the smallest start lacking a kind is printed.

    python3 k4/oc1max_multi/lift.py FILE.jsonl   (lines with sets, vals, picks; e.g. walk_fail.py output)
"""
import sys, os, json, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, frozen, dangerous, oa_absorbers, moves, is_canonical
from dred import obstacles
from lemma_b import truly_dangerous


def canon_at(I, B, desc):
    """desc is a chain that is canonical at state B (single-good bases along it, no junk for x_i, i >= 1)"""
    kind, path, Hs = desc
    if kind != 'chain': return False
    t = len(path) - 1
    if any(Hs.get(i) for i in range(1, t + 1)): return False
    val = [I.V(i, B[i]) for i in range(I.n)]
    for i in range(1, t + 1):
        b = B[path[i - 1]]
        if len(b) != 1 or I.v[path[i]].get(b[0], 0) <= val[path[i]]: return False
    return path[-1] not in frozen(I, B)


def study(rec):
    I = Inst(rec['sets'], rec['vals']); Y = tuple(rec['picks']); base = base_from_picks(Y)
    J = junk(I, base); F = set(frozen(I, base)); D = dangerous(I, base); DT = truly_dangerous(I, base, D, J)
    tags = set(); first = moves(I, base)
    for B1, ds1 in first.items():
        can1 = [d for d in ds1 if is_canonical(I, base, d, D)]
        if not can1: continue
        sec = None
        for B2, ds2 in moves(I, B1).items():
            if not oa_absorbers(I, B2): continue
            if sec is None: sec = []
            sec.append((B2, ds2))
        if not sec: continue
        tags.add('repair, P1 canonical from D')
        F1 = set(frozen(I, B1))
        for d1 in can1:
            path1 = d1[1]; k = path1[0]; z = path1[-1]
            dem = [q for q in D if q != k and q in F1 and I.threat(q, I.V(q, B1[q]), J + list(base[z]))]
            if set(B1[k]) <= set(J) and len(B1[k]) == 2: tags.add('repair, P1 takes a junk pair')
            for B2, ds2 in sec:
                F2 = set(frozen(I, B2))
                for d2 in ds2:
                    kind2, path2 = d2[0], d2[1]
                    lift = all(q == path2[0] or q not in F2 for q in dem)
                    if lift: tags.add('LIFT')
                    if canon_at(I, B1, d2):
                        tags.add('P2 canonical at B1')
                        if lift: tags.add('LIFT, P2 canonical at B1')
                        if path2[-1] == z: tags.add('P2 canonical at B1, head z')
                    s = path2[0]
                    who = ('DEMAND agent' if s in dem else 'k' if s == k else 'other dangerous' if s in D else
                           'frozen non-dangerous' if s in F else 'unfrozen')
                    tags.add('P2 starts at: ' + who)
    U = [i for i in range(I.n) if i not in F and base[i]]
    return rec, tags, (len(D), len(DT), len(U))


if __name__ == '__main__':
    import gzip
    recs = [json.loads(l) for l in (gzip.open(sys.argv[1], 'rt') if sys.argv[1].endswith('.gz') else open(sys.argv[1]))]
    T = collections.Counter(); ex = {}
    allk = ['repair, P1 canonical from D', 'repair, P1 takes a junk pair', 'LIFT', 'P2 canonical at B1',
            'LIFT, P2 canonical at B1', 'P2 canonical at B1, head z']
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for rec, tags, shape in pool.imap_unordered(study, recs, chunksize=4):
            T['failing starts'] += 1; T['shape (|D|, |D_T|, unfrozen) = %s' % (shape,)] += 1
            for t in tags: T[t] += 1
            for t in allk:
                if t not in tags:
                    n = len(rec['sets'])
                    if t not in ex or n < len(ex[t]['sets']): ex[t] = rec
    print('$ python3 k4/oc1max_multi/lift.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
    for t, r in sorted(ex.items()): print('a start without [%s]:' % t, json.dumps(r))
