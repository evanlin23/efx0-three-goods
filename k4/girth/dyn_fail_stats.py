"""What do the labelings on which DYN's pipeline fails have in common, and what do the stuck states look like?
(k4/girth.md section 5; coordinator's questions.)  EVIDENCE only.

Random strict profiles of random k = 4 cores with n = 3, 4 (results/k4_certs_{3,4}_*.json.gz); every labeling.  Per run:
features of the labeling (vertex 0 on a 2-cycle, on a 3-cycle, its degree and number of private goods) and of the state
after Algorithm 2 with the G1 repair (leftover goods, non-envied agents and how many hold <= 1 good, G1 skips, whether
(4) holds for every agent), and whether dynamic parking completes.  For failing runs, the search's terminal states
(no good can go to any currently non-envied agent) are examined: Lemma SLACK says every non-envied agent there holds
>= 2 goods; the script checks that and records who blocks each placement.

    python3 k4/girth/dyn_fail_stats.py PROFILES SEED
"""
import collections
import itertools
import random
import sys

from lss import Inst, labels, Run, envied, is_efx0, park_dynamic, two_cycles, triangles
from sources import cores, domains


def all_labels(I):
    for z in range(I.n):
        nb = I.neighbours(z)
        rest = [a for a in range(I.n) if a != z and a not in nb]
        for p in itertools.permutations(nb):
            for q in itertools.permutations(rest):
                yield z, labels(I, z, p, q)


def stuck_states(I, X, U, cap=2000):
    """terminal states of the dynamic-parking search (some goods left, no placement possible)"""
    out = []
    seen = set()

    def rec(Y, left):
        key = tuple(frozenset(b) for b in Y)
        if key in seen or len(out) >= cap:
            return
        seen.add(key)
        if not left:
            return
        moved = False
        for g in sorted(left):
            for u in range(I.n):
                if envied(I, Y, u):
                    continue
                Z = [set(b) for b in Y]
                Z[u].add(g)
                if is_efx0(I, Z):
                    moved = True
                    rec(Z, left - {g})
        if not moved:
            out.append(([set(b) for b in Y], set(left)))

    rec([set(b) for b in X], set(U))
    return out


def main():
    per = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    print('$ python3 k4/girth/dyn_fail_stats.py', *sys.argv[1:], flush=True)
    allc = cores(3) + cores(4)
    F = collections.Counter()
    stuck = collections.Counter()
    shown = 0
    for t in range(per):
        f, idx, sets, m = rng.choice(allc)
        D = domains(sets, m)
        ds = [rng.choice(d) for d in D]
        I = Inst([sorted(d) for d in ds], [[d[g] for g in sorted(d)] for d in ds], m)
        two = {a for x, y, sh in two_cycles(I) for a in (x, y)}
        tri = {a for x, y, z, w in triangles(I) for a in (x, y, z)}
        priv = [sum(1 for g in I.R[a] if len(I.edge[g]) == 1) for a in range(I.n)]
        any_ok = False
        runs = []
        for z, lab in all_labels(I):
            r = Run(I, lab)
            r.alg2_safe()
            okstate = is_efx0(I, r.X)
            Z = park_dynamic(I, r.X, r.U) if okstate else None
            ok = Z is not None
            any_ok |= ok
            env = [i for i in range(I.n) if envied(I, r.X, i)]
            N = [u for u in range(I.n) if u not in env]
            feat = {
                'zero on 2-cycle': z in two, 'zero on 3-cycle': z in tri, 'zero degree %d' % len(I.R[z]): True,
                'zero private %d' % priv[z]: True,
                'G1 skipped someone': any(e[0] == 'A2L4s' for e in r.events) and False,
                '(4) fails for someone': any(I.val(i, r.U & I.R[i]) > I.val(i, r.X[i]) for i in range(I.n)),
                'leftovers %d' % min(len(r.U), 4): True,
                'non-envied singletons 0': sum(1 for u in N if len(r.X[u]) <= 1) == 0,
            }
            runs.append((ok, feat, r))
        F['instances'] += 1
        F['instances: some labeling completes'] += any_ok
        for ok, feat, r in runs:
            F['runs'] += 1
            F['runs failing'] += not ok
            for k, v in feat.items():
                if v:
                    F[('all', k)] += 1
                    if not ok:
                        F[('fail', k)] += 1
            if not ok:
                for Y, left in stuck_states(I, r.X, r.U, cap=50):
                    stuck['stuck states'] += 1
                    envd = [i for i in range(I.n) if envied(I, Y, i)]
                    N = [u for u in range(I.n) if u not in envd]
                    stuck['every non-envied agent holds >= 2 goods (Lemma SLACK)'] += all(len(Y[u]) >= 2 for u in N)
                    stuck['no non-envied agent at all'] += not N
                    stuck['left %d' % len(left)] += 1
                if shown < 3:
                    shown += 1
                    print('failing run:', I, 'labels', r.lab, 'state', [sorted(b) for b in r.X], 'U', sorted(r.U),
                          flush=True)
    print('runs', F['runs'], 'failing', F['runs failing'], '; instances', F['instances'], 'some labeling completes',
          F['instances: some labeling completes'])
    keys = sorted({k[1] for k in F if isinstance(k, tuple)})
    print('%-34s %9s %9s %9s' % ('feature of the run', 'runs', 'failing', 'fail rate'))
    for k in keys:
        a, b = F[('all', k)], F[('fail', k)]
        print('%-34s %9d %9d %8.2f%%' % (k, a, b, 100.0 * b / a if a else 0))
    print('overall fail rate %.2f%%' % (100.0 * F['runs failing'] / F['runs']))
    print('stuck states of failing runs:', dict(stuck), flush=True)


if __name__ == '__main__':
    main()
