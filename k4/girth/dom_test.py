"""Conjecture DOM (k4/girth.md section 6): for EVERY labeling, the state X left by LSS's Algorithm 2 with the G1 repair
has a DOMINATING completion: a complete EFX0 allocation Z with v_i(Z_i) >= v_i(X_i) for every agent i.  (The parking
searches of DYN only reach some of these; on the runs where every DYN move set fails, dominating completions exist.)
EVIDENCE only: random strict profiles of random cores, every labeling, brute force over all n^m allocations.

    python3 k4/girth/dom_test.py N SEED SECS [MAXM]
Prints every state without a dominating completion.
    python3 k4/girth/dom_test.py exhaustive N [JOBS] [MAXM]
CERTIFIES DOM for every labeling on every strict profile of every core with n = N (m <= MAXM), by the covering of
dyncert.py (the brute force runs through recorded comparisons).
"""
import collections
import itertools
import random
import sys
import time

from lss import Inst, Run, labels
from sources import cores, domains


def dominating_completion(I, X):
    """brute force; returns a dominating complete EFX0 allocation or None"""
    n, m = I.n, I.m
    base = [I.val(i, X[i]) for i in range(n)]
    v = [[I.v[i].get(g, 0) for g in range(m)] for i in range(n)]
    for asg in itertools.product(range(n), repeat=m):
        val = [0] * n
        for g, a in enumerate(asg):
            val[a] += v[a][g]
        if any(val[i] < base[i] for i in range(n)):
            continue
        # EFX0: for all i != j, for every g in Z_j: v_i(Z_j - g) <= v_i(Z_i)
        ok = True
        for j in range(n):
            Zj = [g for g in range(m) if asg[g] == j]
            if not Zj:
                continue
            for i in range(n):
                if i == j:
                    continue
                s = sum(v[i][g] for g in Zj)
                if s - min(v[i][g] for g in Zj) > val[i]:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return [frozenset(g for g in range(m) if asg[g] == i) for i in range(n)]
    return None


def all_labels(I):
    for z in range(I.n):
        nb = I.neighbours(z)
        rest = [a for a in range(I.n) if a != z and a not in nb]
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                yield labels(I, z, p, q)


def main():
    N, seed, secs = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    maxm = int(sys.argv[4]) if len(sys.argv) > 4 else 99
    rng = random.Random(seed)
    print('$ python3 k4/girth/dom_test.py', *sys.argv[1:], flush=True)
    allc = [c for c in cores(N) if c[3] <= maxm]
    C = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        f, idx, sets, m = rng.choice(allc)
        D = domains(sets, m)
        ds = [rng.choice(d) for d in D]
        I = Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m)
        C['profiles'] += 1
        seen = {}
        for lab in all_labels(I):
            r = Run(I, lab, check=False)
            r.alg2_safe()
            key = tuple(r.X)
            C['runs'] += 1
            if key not in seen:
                seen[key] = dominating_completion(I, r.X) is not None
                C['distinct states'] += 1
            if not seen[key]:
                C['NO DOMINATING COMPLETION'] += 1
                print('NO DOMINATING COMPLETION', I, 'labels', lab, 'state', [sorted(b) for b in r.X], 'U',
                      sorted(r.U), flush=True)
        if C['profiles'] % 500 == 0:
            print(dict(C), flush=True)
    print('total', dict(C), flush=True)


if __name__ == '__main__' and sys.argv[1] != 'exhaustive':
    main()


# ---------------------------------------------------------------- exhaustive version (covering, as dyncert.py)

def _drun_class():
    import dyncert as D

    class DRun(D.FastRun):
        """Algorithm 2 with the G1 repair, then: is there a dominating complete EFX0 allocation?  Every test is a
        recorded comparison, so the covering of dyncert.py applies."""

        def go(self):
            C = self.C
            X = [0] * C.n
            U = [(1 << C.m) - 1]
            self.alg2_safe(X, U)
            if not self.efx0(X):
                return False
            for asg in itertools.product(range(C.n), repeat=C.m):
                Z = [0] * C.n
                for g, a in enumerate(asg):
                    Z[a] |= 1 << g
                if all(self.cmp(i, Z[i], X[i]) >= 0 for i in range(C.n)) and self.efx0(Z):
                    return True
            return False

    return DRun


def every_labeling_exhaustive(task):
    """per core and labeling: does DOM hold on every strict profile?  (covering with that labeling alone, stopping at
    the first failing class)"""
    import dyncert as D
    name, sets, m = task
    DRun = _drun_class()
    t0 = time.time()
    doms = domains(sets, m)
    C = D.Core(sets, m, doms)
    L = D.labelings(C, 'all')
    bad, runs = [], 0
    for lab in L:
        work = [tuple(C.full)]
        while work:
            box = work.pop()
            if any(b == 0 for b in box):
                continue
            rep = [D.lowbit_index(b) for b in box]
            r = DRun(C, rep, lab)
            ok = r.go()
            runs += 1
            if not ok:
                bad.append((lab, [dict(sorted(doms[i][rep[i]].items())) for i in range(C.n)]))
                break
            cls = r.box(box)
            for a in range(C.n):
                rest = box[a] & ~cls[a]
                if rest:
                    work.append(tuple(cls[:a]) + (rest,) + tuple(box[a + 1:]))
    return dict(name=name, nlab=len(L), bad=bad, runs=runs, time=time.time() - t0)


def main_exhaustive():
    import multiprocessing as mp
    N = int(sys.argv[2])
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else mp.cpu_count()
    maxm = int(sys.argv[4]) if len(sys.argv) > 4 else 99
    tasks = [('%s#m%d#%d' % (f, m, idx), sets, m) for f, idx, sets, m in cores(N) if m <= maxm]
    print('$ python3 k4/girth/dom_test.py exhaustive', *sys.argv[2:], '(%d cores)' % len(tasks), flush=True)
    t0 = time.time()
    tot = collections.Counter()
    with mp.Pool(jobs) as pool:
        for res in pool.imap_unordered(every_labeling_exhaustive, tasks):
            tot['cores'] += 1
            tot['labelings'] += res['nlab']
            tot['labelings failing somewhere'] += len(res['bad'])
            tot['runs'] += res['runs']
            print('%-28s labelings %3d, DOM fails for %d, runs %8d %.1fs' % (res['name'], res['nlab'], len(res['bad']),
                                                                             res['runs'], res['time']), flush=True)
            for lab, P in res['bad'][:3]:
                print('    DOM FAILS: labels', lab, 'profile', P, flush=True)
    print('TOTAL', dict(tot), '%.0fs' % (time.time() - t0), flush=True)


if __name__ == '__main__' and sys.argv[1] == 'exhaustive':
    main_exhaustive()
