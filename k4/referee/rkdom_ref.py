#!/usr/bin/env python3
"""Referee check of the rkmax session's Conjecture RKDOM and Lemmas TC / COMP / PO / 2AG on data (k4/rkmax.md on
proof/k4-rkmax at ebd17e7e). Own code (cert_ref.py, rkmax_ref.py); nothing from k4/rkmax/ is run.

Per profile of an export: ALL maximum matchings (agents to relevant goods, by direct enumeration, not through SD
orders), their rank vectors (rank_i = 1 + #goods i values above its good, 5 if unmatched).
  - every exported failing start Y: is some maximum matching rank-dominating it (sorted rank vector pointwise <=, and
    different)? the least number of agents a dominating matching changes;
  - every undominated maximum matching: is it an SD outcome (PO + SDPO), and does it satisfy OC1 (rkmax_ref.oc1)?
  - (on every 20th profile) COMP on the data: at every sigma-maximal maximum matching, no single alternating component raises sigma (checked
    as: no maximum matching differing from it on one component of the symmetric difference has larger sigma), and at
    every non-maximal one, some single component raises sigma;
  - 2AG: for every two-agent change between maximum matchings, its formula for "dominates" and "raises sigma" equals
    the direct comparison.
    python3 rkdom_ref.py EXPORT [JOBS] [STRIDE]"""
import sys, gzip, json, itertools
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import sd, mk, rel
from rkmax_ref import oc1

def ranks(v, M):
    return tuple(5 if M[i] is None else 1 + sum(1 for g in rel(v, i) if v[i][g] > v[i][M[i]]) for i in range(len(v)))

def sig(r):
    return tuple(sum(1 for x in r if x == k) for k in (1, 2, 3, 4))

def dominates(r2, r1):
    a, b = sorted(r2), sorted(r1)
    return all(x <= y for x, y in zip(a, b)) and a != b

def matchings(v):
    n = len(v); R = [sorted(rel(v, i)) for i in range(n)]
    out = []
    def rec(i, used, M):
        if i == n:
            out.append(tuple(M)); return
        rec(i + 1, used, M + [None])
        for g in R[i]:
            if g not in used:
                rec(i + 1, used | {g}, M + [g])
    rec(0, frozenset(), [])
    best = max(sum(1 for x in M if x is not None) for M in out)
    return [M for M in out if sum(1 for x in M if x is not None) == best]

def components(M1, M2):
    """agent sets of the components of the symmetric difference (agents whose goods differ, linked by shared goods)"""
    n = len(M1); diff = [i for i in range(n) if M1[i] != M2[i]]
    parent = {i: i for i in diff}
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    owner1 = {g: i for i, g in enumerate(M1) if g is not None}
    for i in diff:
        g = M2[i]
        if g is not None and g in owner1 and owner1[g] in parent:
            parent[find(i)] = find(owner1[g])
    comps = {}
    for i in diff:
        comps.setdefault(find(i), []).append(i)
    return list(comps.values())

def job(task):
    sets, vals, fails, deep = task
    v = mk(sets, vals); n = len(v); c = Counter()
    MMs = matchings(v)
    rk = {M: ranks(v, M) for M in MMs}
    sdset = set(tuple(sd(v, list(o))) for o in itertools.permutations(range(n)))
    c['profiles'] += 1; c['maximum matchings'] += len(MMs)
    for Y in fails:
        Y = tuple(Y)
        doms = [M for M in MMs if dominates(rk[M], rk[Y])]
        c['failing starts'] += 1
        if not doms:
            c['  FAILING START NOT DOMINATED'] += 1; continue
        k = min(sum(1 for i in range(n) if M[i] != Y[i]) for M in doms)
        c['  dominated; least dominating change: %d agents' % k] += 1
    und = [M for M in MMs if not any(dominates(rk[M2], rk[M]) for M2 in MMs)]
    c['undominated maximum matchings'] += len(und)
    for M in und:
        c['  undominated: SD outcome %s' % (M in sdset)] += 1
        c['  undominated: OC1 holds' if oc1(v, list(M)) is not None else '  undominated: OC1 FAILS'] += 1
    if not deep:
        return c
    c['profiles with the COMP / 2AG checks'] += 1
    smax = max(sig(rk[M]) for M in MMs)
    for M in MMs:
        better_single = False
        for M2 in MMs:
            if sig(rk[M2]) > sig(rk[M]) and len(components(M, M2)) == 1:
                better_single = True; break
        ismax = sig(rk[M]) == smax
        c['COMP: sigma-max, no single component raises' if ismax and not better_single else
          ('COMP: not max, a single component raises' if (not ismax) and better_single else
           'COMP VIOLATION (max %s, single raise %s)' % (ismax, better_single))] += 1
        for M2 in MMs:
            ch = [i for i in range(n) if M[i] != M2[i]]
            if len(ch) != 2:
                continue
            r1, r2 = rk[M], rk[M2]
            gain = [i for i in ch if r2[i] < r1[i]]; lose = [i for i in ch if r2[i] > r1[i]]
            if len(gain) != 1 or len(lose) != 1:
                continue
            a, b = gain[0], lose[0]
            ra, ra2, rb, rb2 = r1[a], r2[a], r1[b], r2[b]
            f_dom = ra2 <= rb and rb2 <= ra and not (ra2 == rb and rb2 == ra)
            f_sig = ra2 < rb or (ra2 == rb and rb2 < ra)
            c['2AG: formula = direct' if (f_dom == dominates(r2, r1) and f_sig == (sig(r2) > sig(r1)))
              else '2AG: MISMATCH'] += 1
    return c

def main():
    path = sys.argv[1]; jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    stride = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    print('$ python3 k4/referee/rkdom_ref.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(path)); prof = {}
    for h in d['hypergraphs']:
        for s in h['starts']:
            prof.setdefault(json.dumps([h['sets'], s['vals']]), (h['sets'], s['vals'], []))[2].append(s['picks'])
    tasks = [prof[k] + (t % 20 == 0,) for t, k in enumerate(sorted(prof))][::stride]
    print('profiles in export %d, this run %d' % (len(prof), len(tasks)), flush=True)
    C = Counter()
    with Pool(jobs) as p:
        for c in p.imap_unordered(job, tasks, chunksize=20):
            C.update(c)
    for k in sorted(C):
        print('  %-55s %d' % (k, C[k]))

if __name__ == '__main__':
    main()
