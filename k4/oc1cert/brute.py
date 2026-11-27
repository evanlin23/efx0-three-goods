"""Brute-force checks of OC1^max for every strict profile at n <= 3 (workstream compute/k4-oc1max-cert), no SAT.

Mode raw (no certificate):
- For every type profile of the hypergraph (types of k4/oc1cert/check.py, its own enumeration) and every order, take
  the raw SD picks.
- When they form a maximum matching, run the coordinator's raw checker k4/sdc/oc1_mc2_rand.Inst.check.  It does its
  own SD, every official move, and a brute-force one-absorber completion.
- No start may return 'OC1 fails'.  Only feasible when the profile space is small: --maxprof bounds it.

Mode cover (certificate, exhaustive over profiles):
- For every maximum matching Y, take the witnesses whose move is legal from Y and whose X fits (check.Hyper.apply and
  shape_ok).  Each one is a box over the type profiles: one mask per agent, from raw integer evaluation.
- For every order, the SD region of Y is again a box: agent i at its position picks Y_i under type t, given the earlier
  agents' picks.
- The check is that every region box lies inside the union of the witness boxes.  This is computed exactly, profile
  by profile, as a dense boolean array: agent 0's type times a boolean matrix product over agents 1 and 2.

    python3 k4/oc1cert/brute.py raw LIST [--maxprof=N]
    python3 k4/oc1cert/brute.py cover CERT.json.gz"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from check import Hyper


def raw_job(args):
    lst, idx, sets, maxprof = args
    from oc1_mc2_rand import Inst
    H = Hyper(sets); n = H.n
    sizes = [len(T) for T in H.types]
    if np.prod(sizes) > maxprof: return lst, idx, sets, 'skipped', collections.Counter()
    nu, _ = H.picks_all()
    C = collections.Counter(); bad = []
    for prof in itertools.product(*[range(s) for s in sizes]):
        vals = [[H.types[i][t][g] for g in H.sets[i]] for i, t in enumerate(prof)]
        I = Inst(sets, vals)
        outs = set(I.sd(o) for o in itertools.permutations(range(n)))
        for Y in outs:
            if sum(y is not None for y in Y) != nu: C['non-max SD outcomes'] += 1; continue
            r = I.check(Y); C[r] += 1
            if r == 'OC1 fails': bad.append((vals, Y))
        C['profiles'] += 1
    return lst, idx, sets, ('FAIL %s' % json.dumps(bad[:3]) if bad else 'ok'), C


def region_masks(H, Y, order):
    taken = set(); out = [None] * H.n
    for i in order:
        S = [g for g in H.sets[i] if g not in taken]
        m = np.zeros(len(H.types[i]), dtype=bool)
        for t, v in enumerate(H.types[i]):
            pick = max(S, key=lambda g: v[g]) if S else None
            m[t] = pick == Y[i]
        out[i] = m
        if Y[i] is not None: taken.add(Y[i])
    return out


def cover_job(rec):
    t0 = time.time()
    H = Hyper(rec['sets']); n = H.n
    if n > 3: return rec['list'], rec['idx'], 'skipped (n > 3)', collections.Counter(), 0
    nu, Ys = H.picks_all()
    Ws = rec['witnesses']
    C = collections.Counter()
    for Y in Ys:
        boxes = []
        for w in Ws:
            r = H.apply(Y, w)
            if r is None: continue
            X = [int(c) for c in w['X']]
            if not H.shape_ok(r[0], X): continue
            masks = H.efx0_masks(X)
            for x, new, old in r[1]: masks[x] = masks[x] & (H.val(x, new) > H.val(x, old))
            boxes.append(masks)
        C['boxes'] += len(boxes)
        sizes = [len(T) for T in H.types]
        if boxes:
            M = [np.array([b[i] for b in boxes], dtype=np.int32) for i in range(n)]   # (boxes, types_i)
        if n == 2:
            cov = (M[0].T @ M[1] > 0) if boxes else np.zeros(sizes, dtype=bool)
        else:
            cov = np.zeros(sizes, dtype=bool)
            if boxes:
                for t in range(sizes[0]):
                    sel = M[0][:, t] > 0
                    if sel.any(): cov[t] = (M[1][sel].T @ M[2][sel]) > 0
        for order in itertools.permutations(range(n)):
            A = region_masks(H, Y, order)
            if not all(a.any() for a in A): continue
            C['nonempty (order, matching) regions'] += 1
            sub = cov[np.ix_(*[np.flatnonzero(a) for a in A])]
            C['profiles x orders checked'] += sub.size
            if not sub.all():
                bad = np.argwhere(~sub)[0]
                prof = [np.flatnonzero(a)[k] for a, k in zip(A, bad)]
                vals = [[H.types[i][t][g] for g in H.sets[i]] for i, t in enumerate(prof)]
                return rec['list'], rec['idx'], 'UNCOVERED %s' % json.dumps({'picks': Y, 'order': order, 'vals': vals}), C, time.time() - t0
    return rec['list'], rec['idx'], 'covered', C, time.time() - t0


def main():
    mode = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--') and '=' in a)
    args = [a for a in sys.argv[2:] if not a.startswith('--')]
    print('$ python3 k4/oc1cert/brute.py', *sys.argv[1:], flush=True)
    T = collections.Counter(); t0 = time.time(); ok = True
    procs = int(os.environ.get('PROCS', mp.cpu_count()))
    if mode == 'raw':
        maxprof = int(opt.get('maxprof', 10 ** 6))
        tasks = []
        for lst in args[0].split(','):
            for c in json.load(gzip.open(os.path.join(ROOT, 'results', 'k4_certs_%s.json.gz' % lst)))['cores']:
                tasks.append((lst, c['idx'], c['sets'], maxprof))
        with mp.Pool(procs) as pool:
            for lst, idx, sets, res, C in pool.imap_unordered(raw_job, tasks):
                T['hypergraphs ' + res.split()[0]] += 1
                for k, c in C.items(): T[k] += c
                if res.startswith('FAIL'): ok = False; print('FAIL', lst, idx, sets, res, flush=True)
                if res == 'skipped': print('skipped (profile space > %d)' % maxprof, lst, idx, sets, flush=True)
    else:
        recs = json.load(gzip.open(args[0]))['cores']
        with mp.Pool(procs) as pool:
            for lst, idx, res, C, dt in pool.imap_unordered(cover_job, [r for r in recs if r['result'] == 'certified']):
                T['hypergraphs ' + res.split()[0]] += 1
                for k, c in C.items(): T[k] += c
                if res.startswith('UNCOVERED'): ok = False; print(lst, idx, res, flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
    print('RESULT', 'ok' if ok else 'FAILED')


if __name__ == '__main__':
    main()
