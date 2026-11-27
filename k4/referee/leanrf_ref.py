#!/usr/bin/env python3
"""Conjecture RF in Lean's amended form (formal/k4-rf, PR #147: `Receiver` = an agent nobody wants the pick of, so every
pickless agent is a receiver; `ConjRFWith`: at every OC1-failing maximum-matching start, EVERY receiver u satisfies
ReceiverFirst = some u-first order gives a maximum matching, and every u-first maximum-matching order satisfies OC1).
Coordinator's question (2026-11-27 06:14): do OC1-failing maximum-matching starts with nu < n exist, and at any that
do, does ReceiverFirst hold for the pickless receivers?

Random strict k = 4 cores in Lean's IsCore4 sense (3-4 goods each; 2 v_i(g) < v_i(R_i); at most |R_i| - 2 private
goods; two private goods worth less than the shared ones; every good valued), connected, forced to have nu < n by a
tight set: s agents (s = 4 or 5) whose goods all lie in s - 1 goods. All orders; OC1 by rkmax_ref.oc1 (additions,
chains, rings; one-absorber completion). Own code.
    python3 leanrf_ref.py N SEED N_AGENTS [JOBS]
    python3 leanrf_ref.py cores5 TRIALS      (run from the repository root)"""
import sys, random, itertools, json
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import sd, nu
from rkmax_ref import oc1

def strict_vals(rng, k):
    while True:
        vals = [rng.randint(1, 40) for _ in range(k)]
        sums = [sum(c) for r in range(1, k + 1) for c in itertools.combinations(vals, r)]
        if len(set(sums)) == len(sums) and all(2 * x < sum(vals) for x in vals):
            return vals

def gen(rng, n):
    s = rng.choice([4, 5]) if n >= 5 else 4
    s = min(s, n)
    m = rng.randint(n, n + 4)
    G_T = list(range(s - 1))
    R = []
    for i in range(n):
        if i < s:
            R.append(sorted(rng.sample(G_T, rng.randint(3, min(4, len(G_T))))))
        else:
            R.append(sorted(rng.sample(range(m), rng.randint(3, 4))))
    v = [[0] * m for _ in range(n)]
    for i in range(n):
        for g, a in zip(R[i], strict_vals(rng, len(R[i]))):
            v[i][g] = a
    return v

def is_core(v):
    n = len(v); m = len(v[0])
    if not all(any(v[i][g] for i in range(n)) for g in range(m)):
        return False
    for i in range(n):
        Ri = [g for g in range(m) if v[i][g] > 0]
        priv = [g for g in Ri if not any(j != i and v[j][g] > 0 for j in range(n))]
        if not (3 <= len(Ri) <= 4) or len(priv) + 2 > len(Ri):
            return False
        if len(priv) == 2 and sum(v[i][g] for g in priv) >= sum(v[i][g] for g in Ri if g not in priv):
            return False
    seen = {0}; st = [0]
    while st:
        i = st.pop()
        for j in range(n):
            if j not in seen and any(v[i][g] and v[j][g] for g in range(m)):
                seen.add(j); st.append(j)
    return len(seen) == n

def wants(v, Y, a, j):
    return Y[j] is not None and v[a][Y[j]] > (v[a][Y[a]] if Y[a] is not None else 0)

def job(args):
    seed, N, n = args
    rng = random.Random(seed); c = Counter(); ex = []
    for t in range(N):
        v = gen(rng, n)
        if not is_core(v):
            continue
        c['cores (nu < n forced)'] += 1
        N0 = nu(v)
        if N0 >= n:
            continue
        c['cores with nu < n'] += 1
        sdv = {}
        for o in itertools.permutations(range(n)):
            sdv[o] = tuple(sd(v, list(o)))
        mm = {o: Y for o, Y in sdv.items() if sum(1 for y in Y if y is not None) == N0}
        st = {}
        for Y in set(mm.values()):
            st[Y] = oc1(v, list(Y))
        c['MM starts (distinct vectors)'] += len(st)
        fails = [Y for Y in st if st[Y] is None]
        c['MM starts failing OC1'] += len(fails)
        for Y in fails:
            recv = [u for u in range(n) if not any(i != u and wants(v, Y, i, u) for i in range(n))]
            pickless = [u for u in recv if Y[u] is None]
            c['  failing: receivers that hold a pick %d, pickless %d' % (len(recv) - len(pickless), len(pickless))] += 1
            for u in recv:
                uf = [o for o in mm if o[0] == u]
                exists = bool(uf)
                allok = all(st[mm[o]] is not None for o in uf)
                kind = 'pickless' if Y[u] is None else 'pick-holding'
                c['  %s receiver: some u-first MM order %s, all u-first MM orders OC1 %s' % (kind, exists, allok)] += 1
                if not (exists and allok) and len(ex) < 2:
                    ex.append(dict(v=v, Y=list(Y), u=u, kind=kind, exists=exists, allok=allok))
            some = any(bool([o for o in mm if o[0] == u]) and all(st[mm[o]] is not None for o in mm if o[0] == u) for u in recv)
            c['  RF-exists (some receiver works) %s' % some] += 1
    return c, ex

def cores5(trials):
    """The n = 5 connected k = 4 cores (K4.R5, R5c, R5d, R5p lists in results/k4_certs_5_*.json.gz): their nu, and for
    every core with nu < 5, random strict balanced profiles, all 120 orders: every MM start completes at the picks?"""
    import gzip
    from cert_ref import complete
    rng = random.Random(1); c = Counter()
    for tag in ['n4_1', 'n4_2', 'n4_3', 'n4_4', 'pure']:
        d = json.load(gzip.open('results/k4_certs_5_%s.json.gz' % tag))
        for h in d['cores']:
            sets = h['sets']; m = 1 + max(max(x) for x in sets); n = len(sets)
            v0 = [[1 if g in sets[i] else 0 for g in range(m)] for i in range(n)]
            k = nu(v0); c['cores, nu = %d' % k] += 1
            if k == n:
                continue
            c['  nu < 5 core with m = %d' % m] += 1
            for t in range(trials):
                v = [[0] * m for _ in range(n)]
                for i in range(n):
                    for g, a in zip(sets[i], strict_vals(rng, len(sets[i]))):
                        v[i][g] = a
                for o in itertools.permutations(range(n)):
                    Y = sd(v, list(o))
                    if sum(1 for y in Y if y is not None) != k:
                        continue
                    c['  MM starts tested'] += 1
                    B = [({y} if y is not None else set()) for y in Y]
                    c['  ... complete at the picks' if complete(v, B) is not None else '  ... DO NOT COMPLETE'] += 1
    for key in sorted(c):
        print('  %-50s %d' % (key, c[key]))

def main():
    if sys.argv[1] == 'cores5':
        print('$ python3 k4/referee/leanrf_ref.py', *sys.argv[1:], flush=True)
        cores5(int(sys.argv[2])); return
    N, seed, n = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    jobs = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    print('$ python3 k4/referee/leanrf_ref.py', *sys.argv[1:], flush=True)
    chunks = 40
    tasks = [(seed * 1000 + k, N // chunks, n) for k in range(chunks)]
    C = Counter(); EX = []
    with Pool(jobs) as p:
        for c, ex in p.imap_unordered(job, tasks):
            C.update(c); EX += ex
    for k in sorted(C):
        print('  %-90s %d' % (k, C[k]))
    for e in EX[:3]:
        print('  example', json.dumps(e))

if __name__ == '__main__':
    main()
