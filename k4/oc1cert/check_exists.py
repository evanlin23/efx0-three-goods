"""Independent checker for the OC1^∃max certificates of k4/oc1cert/exists.py (workstream compute/k4-oc1max-cert).

It uses check.py's machinery, which shares no code with cegar.py or exists.py: its own types, raw move rules and raw
EFX0.  For each hypergraph:
- ν comes from check.py's brute force over pick vectors.
- Every entry (order pi, picks Y, witness W) is validated combinatorially: Y is a matching of relevant goods with ν
  picks, W's moves are legal from Y by the raw rules, and X contains the moved bases with at most one absorber.
- The entry then becomes a box over the type profiles. Agent i's mask is the set of types under which, at its turn
  in pi (after the earlier agents' picks Y), its favourite remaining good is Y_i (no remaining good, if Y_i is none),
  intersected with W's improving conditions and EFX0 of X.
- After an exact type-class reduction, it decides whether some profile lies outside every box.
  - By default Glucose decides it.  Each distinct agent mask gets its own literal (y <-> the agent's type lies in the
    mask), and each box becomes the clause "some agent's y is false".
  - With ENGINE=dense and n <= 4 it is instead an exhaustive dense check: boolean matrix products over class tuples,
    no SAT.  This is only practical when there are few classes.
  - No profile outside: every profile has an order whose maximum-matching picks satisfy OC1.

    python3 k4/oc1cert/check_exists.py CERT.json.gz"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import numpy as np
from pysat.solvers import Glucose4

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from check import Hyper


def region_masks(H, Y, order):
    taken = set(); out = [None] * H.n
    for i in order:
        S = [g for g in H.sets[i] if g not in taken]
        out[i] = np.array([(max(S, key=lambda g: v[g]) if S else None) == Y[i] for v in H.types[i]], dtype=bool)
        if Y[i] is not None: taken.add(Y[i])
    return out


def check_core(rec):
    t0 = time.time()
    H = Hyper(rec['sets']); n = H.n
    nu, _ = H.picks_all()
    boxes = []; bad = 0
    for e in rec['entries']:
        Y = tuple(e['picks']); order = e['order']; w = e['witness']
        ok = (sorted(order) == list(range(n)) and len([y for y in Y if y is not None]) == nu
              and len(set(y for y in Y if y is not None)) == nu
              and all(y is None or y in H.R[i] for i, y in enumerate(Y)))
        r = H.apply(Y, w) if ok else None
        X = [int(c) for c in w['X']]
        if r is None or not H.shape_ok(r[0], X): bad += 1; continue
        masks = H.efx0_masks(X)
        for x, new, old in r[1]: masks[x] = masks[x] & (H.val(x, new) > H.val(x, old))
        reg = region_masks(H, Y, order)
        boxes.append([masks[i] & reg[i] for i in range(n)])
    cls = []
    for i in range(n):
        sig = collections.defaultdict(list)
        for t in range(len(H.types[i])): sig[tuple(bool(b[i][t]) for b in boxes)].append(t)
        cls.append(list(sig.items()))
    if os.environ.get('ENGINE', 'sat') == 'dense' and n <= 4:
        return dense(rec, H, cls, boxes, bad, t0)
    S = Glucose4(); top = [0]
    def new():
        top[0] += 1; return top[0]
    z = [[new() for _ in c] for c in cls]
    for zi in z:
        S.add_clause(zi)
        for a, b in itertools.combinations(zi, 2): S.add_clause([-a, -b])
    # one literal per distinct agent mask (y <-> the agent's class lies in the mask), so learned clauses are about masks
    ylit = {}
    def y(i, bi):
        key = (i, tuple(k for k, (sg, ts) in enumerate(cls[i]) if sg[bi]))
        if key not in ylit:
            v = ylit[key] = new()
            S.add_clause([-v] + [z[i][k] for k in key[1]])
            for k in key[1]: S.add_clause([-z[i][k], v])
        return ylit[key]
    for bi in range(len(boxes)):
        S.add_clause([-y(i, bi) for i in range(n)])
    if S.solve():
        mod = set(l for l in S.get_model() if l > 0)
        prof = [cls[i][next(k for k, v in enumerate(zi) if v in mod)][1][0] for i, zi in enumerate(z)]
        vals = [[H.types[i][t][g] for g in H.sets[i]] for i, t in enumerate(prof)]
        S.delete()
        return rec['list'], rec['idx'], False, {'uncovered profile': vals, 'invalid entries': bad}, time.time() - t0
    S.delete()
    return rec['list'], rec['idx'], True, {'entries': len(rec['entries']), 'invalid entries': bad,
                                           'type classes': sum(len(c) for c in cls)}, time.time() - t0


def dense(rec, H, cls, boxes, bad, t0):
    """Exact cover check without SAT for n <= 4: every tuple of type classes must lie in some box.  For each class of
    agent 0 and each class of agent 1, the boxes containing both cover all (agent 2, agent 3) class pairs iff the
    boolean matrix product of their masks is everywhere positive (float32, exact for these sizes)."""
    n = H.n
    M = [np.array([[sg[bi] for sg, ts in cls[i]] for bi in range(len(boxes))], dtype=np.float32).reshape(len(boxes), len(cls[i]))
         for i in range(n)]
    while len(M) < 4:                      # pad to four agents with a single all-true class
        M.append(np.ones((len(boxes), 1), dtype=np.float32))
    for c0 in range(M[0].shape[1]):
        s0 = M[0][:, c0] > 0
        A1, A2, A3 = M[1][s0], M[2][s0], M[3][s0]
        for c1 in range(A1.shape[1]):
            s1 = A1[:, c1] > 0
            cov = (A2[s1].T @ A3[s1]) > 0
            if not cov.all():
                c2, c3 = map(int, np.argwhere(~cov)[0])
                pick = [c0, c1, c2, c3][:n]
                vals = [[H.types[i][cls[i][k][1][0]][g] for g in H.sets[i]] for i, k in enumerate(pick)]
                return rec['list'], rec['idx'], False, {'uncovered profile': vals, 'invalid entries': bad}, time.time() - t0
    return rec['list'], rec['idx'], True, {'entries': len(rec['entries']), 'invalid entries': bad,
                                           'type classes': sum(len(c) for c in cls)}, time.time() - t0


def main():
    print('$ python3 k4/oc1cert/check_exists.py', *sys.argv[1:], flush=True)
    recs = json.load(gzip.open(sys.argv[1]))['cores']
    T = collections.Counter(); ok_all = True; t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for lst, idx, ok, info, dt in pool.imap_unordered(check_core, [r for r in recs if r['result'] == 'certified']):
            T['covered' if ok else 'NOT COVERED'] += 1
            for k in ('entries', 'invalid entries', 'type classes'):
                if k in info: T[k] += info[k]
            if not ok: ok_all = False; print('NOT COVERED', lst, idx, info, flush=True)
    T['not certified by the CEGAR'] = sum(r['result'] != 'certified' for r in recs)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
    print('RESULT', ('every certified hypergraph (%d) has, under every strict profile, an SD order whose maximum-matching '
                     'picks satisfy OC1' % T['covered']) if ok_all else 'FAILED')


if __name__ == '__main__':
    main()
