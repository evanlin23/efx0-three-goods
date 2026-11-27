"""Variant DYN-X of DYN's pipeline (k4/girth.md section 6): dynamic parking with envy-cycle rotation AND exchange moves.

An exchange move lets one agent u replace its bundle X_u by T with v_u(T) > v_u(X_u), where T keeps the goods of X_u
that u does not value and takes any subset of the goods of X_u or of the leftovers that u values; the released goods go
back to the leftovers; the move must keep EFX0 (raw check).  Every move of the search (placement on a non-envied
agent, envy-cycle rotation, exchange) weakly raises every agent's value and strictly raises one, so the search is
finite.  Question: with exchange moves, does EVERY labeling complete (on every strict core profile)?

    python3 k4/girth/dynx.py N [FILE_GLOB_PART] [--jobs=J] [--every=E] [--mode=every|exists] [--base]
mode=every: per core, the labelings that complete on every profile (the covering of dyncert.py with one labeling,
stopping at its first failing class); prints the number of such labelings and a failing profile for each other one.
mode=exists: the covering of dyncert.py (some labeling per profile).
--base: the same with DYN's pipeline (no exchange moves), for comparison.
Classes are sound for the same reason as in dyncert.py (every decision is a recorded comparison of disjoint sets).
"""
import itertools
import multiprocessing as mp
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import dyncert as D  # noqa: E402
from dyncert import bits, lowbit_index, popcount  # noqa: E402


class XRun(D.FastRun):
    def park(self, X, U):
        seen = set()
        C = self.C

        def rec(Y, left):
            if not left:
                return True
            key = (Y, left)
            if key in seen:
                return False
            seen.add(key)
            self.count += 1
            if self.count > D.BUDGET:
                return False
            N = [u for u in range(C.n) if not self.envied(Y, u)]
            for g in sorted(bits(left), key=lambda h: (-C.elen[h], h)):
                for u in N:
                    Z = list(Y)
                    Z[u] = Y[u] | (1 << g)
                    Z = tuple(Z)
                    if self.efx0(Z) and rec(Z, left & ~(1 << g)):
                        return True
            if not N:
                for cyc in self.cycles(Y):
                    Z = list(Y)
                    for t, a in enumerate(cyc):
                        Z[a] = Y[cyc[(t + 1) % len(cyc)]]
                    if rec(tuple(Z), left):
                        return True
            # exchange moves
            for u in range(C.n):
                Rm = C.Rm[u]
                keep = Y[u] & ~Rm
                pool = list(bits((Y[u] | left) & Rm))
                for k in range(len(pool), 0, -1):
                    for Tl in itertools.combinations(pool, k):
                        T = keep | sum(1 << g for g in Tl)
                        if T == Y[u]:
                            continue
                        if self.cmp(u, T, Y[u]) <= 0:
                            continue
                        Z = list(Y)
                        Z[u] = T
                        Z = tuple(Z)
                        if not self.efx0(Z):
                            continue
                        nl = (left | (Y[u] & ~T)) & ~T
                        if rec(Z, nl):
                            return True
            return False

        return rec(tuple(X), U)


RUNCLS = [XRun]


def every_labeling(task):
    name, sets, m = task
    from sources import domains
    t0 = time.time()
    doms = domains(sets, m)
    C = D.Core(sets, m, doms)
    L = D.labelings(C, 'all')
    good, bad, runs = [], [], 0
    for j, lab in enumerate(L):
        work = [tuple(C.full)]
        fail = None
        while work:
            box = work.pop()
            if any(b == 0 for b in box):
                continue
            rep = [lowbit_index(b) for b in box]
            r = RUNCLS[0](C, rep, lab)
            ok = r.go()
            runs += 1
            if not ok:
                fail = rep
                break
            cls = r.box(box)
            for a in range(C.n):
                rest = box[a] & ~cls[a]
                if rest:
                    work.append(tuple(cls[:a]) + (rest,) + tuple(box[a + 1:]))
        if fail is None:
            good.append(j)
        else:
            bad.append((lab, [dict(sorted(doms[i][fail[i]].items())) for i in range(C.n)]))
    return dict(name=name, nlab=len(L), good=good, bad=bad, runs=runs, time=time.time() - t0)


def main():
    n = int(sys.argv[1])
    part = sys.argv[2] if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else ''
    jobs, every, mode = mp.cpu_count(), 1, 'every'
    for a in sys.argv[2:]:
        if a.startswith('--jobs='):
            jobs = int(a[7:])
        if a.startswith('--every='):
            every = int(a[8:])
        if a.startswith('--mode='):
            mode = a[7:]
        if a == '--base':
            RUNCLS[0] = D.FastRun                          # DYN's pipeline without exchange moves, for comparison
    from sources import cores
    tasks = [('%s#m%d#%d' % (f, m, idx), sets, m) for f, idx, sets, m in cores(n) if part in f][::every]
    print('$ python3 k4/girth/dynx.py', *sys.argv[1:], '(%d cores, %d jobs)' % (len(tasks), jobs), flush=True)
    t0 = time.time()
    if mode == 'exists':
        D.FastRun = XRun
        tot = dict(cores=0, certified=0, runs=0)
        with mp.Pool(jobs) as pool:
            for res in pool.imap_unordered(D.certify, [t + ('all', 0) for t in tasks]):
                ok = not res['cex'] and res['covered'] == res['profiles']
                tot['cores'] += 1
                tot['certified'] += ok
                tot['runs'] += res['runs']
                print('%-28s profiles %12d covered %12d runs %8d %s' % (res['name'], res['profiles'], res['covered'],
                      res['runs'], 'CERTIFIED' if ok else 'NOT CERTIFIED'), flush=True)
        print('TOTAL', tot, '%.0fs' % (time.time() - t0), flush=True)
        return
    tot = dict(cores=0, cores_every_labeling=0, labelings=0, labelings_good=0, runs=0)
    with mp.Pool(jobs) as pool:
        for res in pool.imap_unordered(every_labeling, tasks):
            tot['cores'] += 1
            tot['labelings'] += res['nlab']
            tot['labelings_good'] += len(res['good'])
            tot['cores_every_labeling'] += len(res['good']) == res['nlab']
            tot['runs'] += res['runs']
            print('%-28s labelings %3d, complete on every profile %3d, runs %8d %.1fs' % (
                res['name'], res['nlab'], len(res['good']), res['runs'], res['time']), flush=True)
            for lab, P in res['bad'][:2]:
                print('    labels', lab, 'fails on', P, flush=True)
    print('TOTAL', tot, '%.0fs' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
