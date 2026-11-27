"""Search for the exception of the splice (kgen/rounds.md §4.10): a REC-S repair (Theorem REC-S, k4/oc1max_multi.md §12:
E(k) with k taking a pool pair T, then a Theorem S case in the reduced instance) whose final allocation X is NOT a
one-round witness at the original start.  Every REC-S repair is enumerated (every listed order, dangerous k, pool pair
T, Theorem S case; up to CAP per start), using the multi session's own code (k4/oc1max_multi: mmlib, dred, reduce_check,
theorem_s, reduce_s) for the repairs and recs_vs_rndp.structures (written here) for the round test, in three forms:
RNDOZ (own chain), RNDPZ (pooled), WIDE (ends may take released picks too).
Data: the certifier's n = 5 OC1^max failures (field oc1_fails of results/k4_oc1max/n5/5_pure_s5o0_summary.jsonl.gz on
compute/k4-oc1max-cert), the matching session's n = 5 walk starts, and multi's n = 4 REC-S export rows.
    python3 kgen/rounds/splice_search.py KIND FILE [STRIDE] [CAP] [JOBS]     KIND: summary | walk | recs4 | random
    (random: FILE = 'n,m,count,seed', every perfect start of random strict connected k = 4 cores)"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'oc1max_multi'))
import recs_vs_rndp as RV, verify_k4zero as VZ
from mmlib import Inst, base_from_picks, junk, dangerous
from dred import apply_chain
from reduce_check import reduced
from theorem_s import s_cases
from reduce_s import earliest_chain
CAP = 200


def rows_of(kind, fn, stride):
    op = gzip.open if fn.endswith('.gz') else open
    if kind == 'summary':
        out = []
        for l in op(fn, 'rt'):
            x = json.loads(l)
            for f in x.get('oc1_fails') or []: out.append({'list': x['list'], 'idx': x['idx'], 'sets': x['sets'], 'vals': f['vals'], 'picks': f['picks']})
    elif kind == 'walk':
        out = [dict(json.loads(l), list='walk164', idx=t) for t, l in enumerate(op(fn, 'rt')) if l.strip()]
    elif kind == 'random':   # fn = 'n,m,count,seed': every perfect start of random strict connected k = 4 cores
        import random, zclimb, rndlib
        n, m, cnt, seed = map(int, fn.split(',')); rng = random.Random(seed); out = []
        for t in range(cnt):
            Z = zclimb.rand_core(n, m, rng)
            sets = [[g for g in range(m) if Z[i][g] > 0] for i in range(n)]; vals = [[Z[i][g] for g in sets[i]] for i in range(n)]
            res, _ = rndlib.oc1z(Z)
            for r in res:
                if r['perfect']: out.append({'list': 'random%d_%d' % (n, m), 'idx': t, 'sets': sets, 'vals': vals, 'picks': list(r['picks'])})
    else:
        out = [{k: s[k] for k in ('list', 'idx', 'sets', 'vals', 'picks', 'orders')} for s in json.load(op(fn, 'rt'))['starts']]
    return out[::stride]


def dense(sets, vals):
    m = 1 + max(max(s) for s in sets); V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv): V[i][g] = x
    return V


def job(row):
    V = dense(row['sets'], row['vals']); n, m = len(V), len(V[0]); y = tuple(row['picks'])
    orders = row.get('orders') or [list(o) for o in itertools.permutations(range(n)) if tuple(VZ.sd(V, o)) == y]
    I = Inst(row['sets'], row['vals']); b = base_from_picks(y); J = junk(I, b); D = dangerous(I, b)
    p = [I.V(i, b[i]) for i in range(I.n)]
    reps = []; seenX = set()
    for order in orders:
        for k in D:
            P = earliest_chain(I, b, k, order)
            pool = [g for g in J + list(b[P[-1]]) if g in I.R[k]]
            for T in itertools.combinations(pool, 2):
                if I.V(k, T) <= p[k]: continue
                nb = apply_chain(I, b, P, T); val = [I.V(i, nb[i]) for i in range(I.n)]
                if any(i != k and I.R[i] and any(I.v[i].get(g, 0) >= val[i] for g in T) for i in range(I.n)): continue
                I2, b2, keep = reduced(I, nb, k); goods = [g for g in range(I.m) if g not in set(T)]
                for k2, P2, h, H0, X2, how in s_cases(I2, b2, dangerous(I2, b2), True, True):
                    if X2 is None or not I2.efx0(X2): continue
                    X = [[] for _ in range(I.n)]; X[k] = sorted(T)
                    for j2, i in enumerate(keep): X[i] = sorted(goods[g] for g in X2[j2])
                    if any(I.threat(k, I.V(k, T), X[j]) for j in range(I.n) if j != k) or not I.efx0(X): continue
                    key = tuple(tuple(x) for x in X)
                    rec = {'order': list(order), 'k': k, 'P1': list(P), 'T': sorted(T), 'P2': [keep[a] for a in P2],
                           'H0_2': sorted(goods[g] for g in H0), 'X': X}
                    if key in seenX: continue
                    seenX.add(key); reps.append(rec)
                    if len(reps) >= CAP: break
                if len(reps) >= CAP: break
            if len(reps) >= CAP: break
        if len(reps) >= CAP: break
    out = []
    for r in reps:
        X = r['X']
        res = {f: bool(RV.structures(V, y, X, pooled, wide)) for f, pooled, wide in (('RNDOZ', False, False), ('RNDPZ', True, False), ('WIDE', True, True))}
        res['case'] = splice_case(V, y, r)
        out.append((r, res))
    return row, out


def splice_case(V, y, r):
    """the case of the splice lemma (kgen/rounds.md §4.10) a REC-S repair falls in:
    Yz in T / released; h a pick or junk; u0 keeps its own pick (u0 = z, or u0 = x_l with u_s = x_{l+1})."""
    P1, P2, T, X = r['P1'], r['P2'], set(r['T']), r['X']; z, u0 = P1[-1], P2[0]
    W = set(X[u0]); picks = set(y); n = len(V)
    hold = {g: i for i in range(n) for g in X[i]}
    yz = 'Yz in T' if y[z] in T else 'Yz released'
    extra = [g for i in range(n) if i != u0 for g in X[i] if g not in picks and False]
    # h: the good of J1 + B1[u_s] not in W (given to one other agent)
    keep = 'u0 keeps its pick' if hold[y[u0]] == u0 else 'u0 passes'
    hp = 'h junk'
    for i in range(n):
        if i == u0: continue
        for g in X[i]:
            if g in picks and hold[g] == i and g != y[i]:
                pass
    # h is a pick iff some agent other than u0 and k holds two picks
    twop = [i for i in range(n) if i not in (u0,) and sum(1 for g in X[i] if g in picks) >= 2 and i != P1[0]]
    if twop: hp = 'h a pick'
    # (EX) of Lemma SPLICE: the pickless agent q's pick lies with an agent v that keeps its own pick
    q = [i for i in range(n) if not any(g in picks for g in X[i])]
    ex = 'no EX configuration'
    if q:
        v = hold[y[q[0]]]
        if hold[y[v]] == v: ex = 'EX configuration (q=%s, v=%s)' % ('k' if q[0] == P1[0] else 'u0' if q[0] == u0 else 'other', 'u0' if v == u0 else 'w')
    return (yz, hp, keep, ex)


if __name__ == '__main__':
    kind, fn = sys.argv[1], sys.argv[2]
    STRIDE = int(sys.argv[3]) if len(sys.argv) > 3 else 1; CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    JOBS = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    print('$ python3 kgen/rounds/splice_search.py', *sys.argv[1:], flush=True)
    rows = rows_of(kind, fn, STRIDE); t0 = time.time(); C = collections.Counter(); shown = 0
    with mp.Pool(JOBS) as pool:
        for t, (row, out) in enumerate(pool.imap_unordered(job, rows, chunksize=4)):
            C['starts'] += 1; C['REC-S repairs'] += len(out)
            if not out: C['starts with NO REC-S repair'] += 1
            for r, res in out:
                for f, ok in res.items():
                    if f != 'case': C[(f, 'X is a one-round witness' if ok else 'X is NOT')] += 1
                C[('case',) + res['case'] + ('RNDOZ holds' if res['RNDOZ'] else 'RNDOZ FAILS',)] += 1
                if not res['RNDPZ']:
                    C['SPLICE EXCEPTIONS (X not a ROUND-P witness)'] += 1
                    import rndlib
                    rr = next(q for q in rndlib.oc1z(dense(row['sets'], row['vals']))[0] if list(q['picks']) == list(row['picks']))
                    res['start'] = {k: rr[k] for k in ('EXT1', 'OC1', 'OC1P', 'RND1Z', 'RNDOZ', 'RNDPZ', 'MD')}
                    C[('exception at a start where', 'OC1 holds' if rr['OC1'] else 'OC1 FAILS', 'RNDOZ holds' if rr['RNDOZ'] else 'RNDOZ FAILS')] += 1
                    if shown < 20:
                        shown += 1
                        print('EXCEPTION', json.dumps({'list': row['list'], 'idx': row['idx'], 'sets': row['sets'], 'vals': row['vals'],
                                                       'picks': row['picks'], 'repair': r, 'round': res}), flush=True)
            if not out and C["starts with NO REC-S repair"] <= 50:
                print('NO REC-S REPAIR', json.dumps({k: row[k] for k in ('list', 'idx', 'sets', 'vals', 'picks')}), flush=True)
            if (t + 1) % 500 == 0: print('...', t + 1, dict(C), '%.0fs' % (time.time() - t0), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
