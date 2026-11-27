"""ROUND-RSD restricted to the rounds Lemma SD-E(round) covers (k4/oc1max_multi.md §17).

A round settles K (|K| <= 2) by vertex-disjoint prefixes of earliest-wanter chains E(k) (order restricted to the present
agents), each k taking an improving T_k inside the junk plus its head's pick (|T_k| <= 3, disjoint), with (H) and (L*)
at the round's end, (L*) toward every phantom (earlier ones included), and released head picks worth at most tau to every
phantom ((P3)).  After at most RMAX rounds, the reduced start must complete at once (every one-absorber completion,
lifted, raw EFX0 in the full instance).  SD-E(round) is asserted at every round (a failure is reported).

    RMAX=2 [WITNESS=OUT.json.gz] python3 k4/oc1max_multi/round_e.py ROWS.jsonl[.gz] | EXPORT.json.gz [...]
"""
import sys, os, json, gzip, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, dangerous
from reduce_s import earliest_chain
from round_sde import reduce_many
from sphi import all_oa

RMAX = int(os.environ.get('RMAX', '2'))


def search(I0, I, b, order, agents, goods, fixed, left, C):
    tau = {f: I0.V(f, T) for f, T in fixed.items()}
    if fixed:
        for X in all_oa(I, b):
            A = [list(fixed.get(a, [])) for a in range(I0.n)]
            for j, a in enumerate(agents): A[a] = [goods[g] for g in X[j]]
            if I0.efx0(A): return 0, ([], [sorted(x) for x in A])
    if left == 0: return None
    J = junk(I, b); p = [I.V(i, b[i]) for i in range(I.n)]; D = dangerous(I, b); opts = {}
    for k in D:
        Ek = earliest_chain(I, b, k, order); opts[k] = []
        for t in range(1, len(Ek)):
            P = Ek[:t + 1]; pool = [g for g in J + [b[P[-1]][0]] if g in I.R[k]]
            opts[k] += [(P, T) for r in (2, 3) for T in itertools.combinations(pool, r) if I.V(k, T) > p[k]]
    for size in (1, 2):
        for K in itertools.combinations(D, size):
            for choice in itertools.product(*[opts[k] for k in K]):
                Ps = [c[0] for c in choice]; Ts = [c[1] for c in choice]
                if len(set(a for P in Ps for a in P)) != sum(len(P) for P in Ps): continue
                if len(set(g for T in Ts for g in T)) != sum(len(T) for T in Ts): continue
                nb = [list(x) for x in b]
                for k, P, T in zip(K, Ps, Ts):
                    nb[k] = sorted(T)
                    for i in range(1, len(P)): nb[P[i]] = list(b[P[i - 1]])
                val = [I.V(i, nb[i]) for i in range(I.n)]; taken = set(g for T in Ts for g in T)
                rel = [b[P[-1]][0] for P in Ps if b[P[-1]][0] not in taken]
                if not all(I.v[a].get(y, 0) <= val[a] for y in rel for a in range(I.n) if a not in K and I.v[a].get(y, 0) > p[a]):
                    continue                                                                  # (H)
                if any(I.threat(i, val[i], T) for k, T in zip(K, Ts) for i in range(I.n) if i != k): continue   # (L*)
                newT = {agents[k]: [goods[g] for g in T] for k, T in zip(K, Ts)}
                if any(I0.threat(f, tau[f], T) for f in fixed for T in newT.values()): continue  # (P2) toward earlier phantoms
                f2 = dict(fixed); f2.update(newT); tau2 = {f: I0.V(f, T) for f, T in f2.items()}
                if any(I0.v[f].get(goods[y], 0) > tau2[f] for y in rel for f in f2): continue  # (P3) for released picks
                I2, b2, keep, g2 = reduce_many(I, tuple(tuple(x) for x in nb), K)
                o2 = [keep.index(a) for a in order if a not in K]
                C['rounds tried'] += 1
                if I2.sd(o2) != tuple(x[0] if x else None for x in b2): C['SD-E(round) VIOLATION'] += 1; continue
                r = search(I0, I2, b2, o2, [agents[a] for a in keep], [goods[g] for g in g2], f2, left - 1, C)
                if r is not None:
                    st = [list(f2.get(a, [])) for a in range(I0.n)]
                    for j, a in enumerate(agents):
                        if j not in K: st[a] = [goods[g] for g in nb[j]]
                    rnd = {'settled': [{'k': agents[k], 'T': sorted(goods[g] for g in T), 'P': [agents[a] for a in P]}
                                       for k, P, T in zip(K, Ps, Ts)], 'state': [sorted(x) for x in st]}
                    return r[0] + 1, ([rnd] + r[1][0], r[1][1])
    return None


def study(rec):
    I = Inst(rec['sets'], rec['vals']); b = base_from_picks(tuple(rec['picks'])); C = collections.Counter(); best = None
    orders = rec.get('orders') or [rec['order']]
    wit = None
    for o in orders:
        r = search(I, I, b, list(o), list(range(I.n)), list(range(I.m)), {}, RMAX, C)
        if r is not None and (best is None or r[0] < best): best = r[0]; wit = {'order': list(o), 'rounds': r[1][0], 'alloc': r[1][1]}
        if best == 1: break
    return C, best, wit


if __name__ == '__main__':
    T = collections.Counter(); miss = []; W = []
    for fn in sys.argv[1:]:
        if fn.endswith('.json.gz'):            # export format {hypergraphs: [{list, idx, sets, starts: [{vals, picks, orders}]}]}
            d = json.load(gzip.open(fn)); rows = [{'list': hg.get('list'), 'm': hg.get('m'), 'idx': hg.get('idx'), 'sets': hg['sets'],
                                                   'vals': s0['vals'], 'picks': s0['picks'], 'orders': s0['orders']}
                                                  for hg in d['hypergraphs'] for s0 in hg['starts']]
        else:
            rows = [json.loads(l) for l in (gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn))]
        with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
            for (C, r, wit), row in zip(pool.imap(study, rows, chunksize=16), rows):
                T.update(C); T['starts'] += 1; T['rounds needed: %s' % r] += 1
                if r is None: miss.append('%s#%s' % (row.get('list', ''), row.get('idx', '')))
                if os.environ.get('WITNESS'): W.append(dict(row, witness=wit))
    print('$ RMAX=%d python3 k4/oc1max_multi/round_e.py' % RMAX, *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
    print('not repaired:', len(miss), miss[:12])
    if os.environ.get('WITNESS'):
        json.dump({'what': 'round_e.py witnesses: per start, the order, the rounds (settled {k, T, P} in the full instance, '
                           'state after the round) and the final allocation', 'inputs': sys.argv[1:], 'starts': W},
                  gzip.open(os.environ['WITNESS'], 'wt'))
        print('wrote', len(W), 'witnesses to', os.environ['WITNESS'])
