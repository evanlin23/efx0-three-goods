"""Satisfied states (k4/sdc.md §30).  A satisfied state gives every agent its top or a pair of its goods worth more than
its top (so the agent wants no single good), the bases disjoint, and every pair holder has at most one of its other
goods unallocated (so the owner's bundle can never threaten it).  Theorem DT's construction applies to such a state
with any owner holding its top that holds none of a pair holder's other goods (k4/sdc.md §30, Lemma DT*).
Per instance: does a satisfied state exist; does every one have a one-absorber completion (SAT); with the owner
restricted as in Lemma DT*; agent types that block existence.

    python3 k4/sdc/satisfied.py screen|suite|special|logs|cores:FILES N SEED"""
import sys, os, json, itertools, collections, time
import _paths
from sdclib import Enc
from min_frozen import load
from f1_owner import absorber_ok


def options(E, i):
    R = sorted(E.R[i], key=lambda g: -E.v[i][g]); a = R[0]
    return [(a,)] + [P for P in itertools.combinations(R[1:], 2) if E.v[i][P[0]] + E.v[i][P[1]] > E.v[i][a]]


def satisfied_states(E):
    n = E.n; opts = [options(E, i) for i in range(n)]
    out = []
    def rec(i, used, B):
        if i == n:
            ok = True
            for j in range(n):
                if len(B[j]) == 2:
                    rest = [g for g in E.R[j] if g not in B[j]]
                    if sum(1 for g in rest if g not in used) > 1: ok = False; break
            if ok: out.append(list(B))
            return
        for o in opts[i]:
            if not (set(o) & used): rec(i + 1, used | set(o), B + [o])
    rec(0, frozenset(), [])
    return out


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/satisfied.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 6: continue
        E = Enc(sets, vals, m); C['instances'] += 1
        st = satisfied_states(E)
        C['instances with a satisfied state'] += bool(st)
        if not st:
            tops = collections.Counter(sorted(E.R[i], key=lambda g: -E.v[i][g])[0] for i in range(n))
            noP = [i for i in range(n) if len(options(E, i)) == 1]
            C['  no satisfied state; some top shared by two agents without a satisfying pair'] += any(
                sum(1 for i in noP if sorted(E.R[i], key=lambda g: -E.v[i][g])[0] == t) >= 2 for t in tops)
            continue
        good_any = good_lemma = True
        for B in st[:40]:
            base = [-1] * m
            for i, b in enumerate(B):
                for g in b: base[g] = i
            base = tuple(base)
            owners = [o for o in range(n) if absorber_ok(E, base, o)]
            if not owners: good_any = False
            pairs = [j for j in range(n) if len(B[j]) == 2]
            allowed = [o for o in range(n) if len(B[o]) == 1 and
                       not any(g in B[o] for j in pairs for g in E.R[j] if g not in B[j])]
            if allowed and not all(o in owners for o in allowed): good_lemma = False
            if not allowed: C['  states with no owner allowed by Lemma DT*'] += 1
        C['  every satisfied state (first 40) has a one-absorber completion'] += good_any
        C['  Lemma DT*: every allowed owner works'] += good_lemma
        if not good_lemma and C['shown'] < 3:
            C['shown'] += 1; print('DT* FAILS', name, json.dumps((sets, vals)), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
