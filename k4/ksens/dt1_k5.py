"""Theorem DT1 at k = 5 (k4/ksens.md §3).  DT1 (k4/sdc.md §30): if SD(pi) has exactly one frozen agent x, wanted by
exactly one agent w, n >= 3, and x values a pair H0 inside J + {Y_w} above Y_x, then the swap (w takes Y_x, x takes H0,
Y_w minus H0 becomes junk) followed by Lemma GDT's completion with ANY owner o outside {x, w} is EFX0.  GDT's
completion: every base kept; x (a pair holder) and nobody else in F gets no junk; every other agent except o at most
one junk good; o the rest.

Random instances (n agents, K relevant goods each); every order; every start in DT1's setting and every improving pair
H0: test GDT's completion for every owner o (SAT, sdclib clauses), and whether any one-absorber completion of the
swapped state exists.

    python3 k4/ksens/dt1_k5.py SEED T n K mmax"""
import sys, json, random, itertools, collections, time
import _paths
import ocsat


def gdt_completion(O, bases, x, o, J):
    """SAT: complete EFX0 allocation keeping bases, x gets no junk, every agent other than o at most one junk good"""
    E = O.E; act = O.new(); cl = []
    for i, b in enumerate(bases):
        for g in b: cl.append([E.x[g][i], -act])
    for g in J:
        cl.append([-E.x[g][x], -act])
        for i in range(O.n):
            if i == o: continue
            for h in J:
                if h > g: cl.append([-E.x[g][i], -E.x[h][i], -act])
    for c in cl: O.S.add_clause(c)
    ok = O.S.solve(assumptions=[act]); O.retire(act); return ok


if __name__ == '__main__':
    seed, T, n, K, mmax = map(int, sys.argv[1:6]); rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/ksens/dt1_k5.py', *sys.argv[1:], flush=True)
    shown = 0
    for t in range(T):
        m = rng.randint(n + 2, mmax)
        sets = [sorted(rng.sample(range(m), K)) for _ in range(n)]
        if len(set().union(*map(set, sets))) < m: continue
        vals = [rng.sample(range(1, 40), K) for _ in sets]
        O = ocsat.OC(sets, vals, m); v = [dict(zip(s, vv)) for s, vv in zip(sets, vals)]
        for Y, order in ocsat.starts(sets, vals, m).items():
            if None in Y: continue
            want = {(i, j) for i in range(n) for j in range(n) if i != j and v[i].get(Y[j], 0) > v[i][Y[i]]}
            frozen = {j for (_, j) in want}
            if len(frozen) != 1: continue
            x = next(iter(frozen)); W = [i for (i, j) in want if j == x]
            if len(W) != 1: continue
            w = W[0]; J = [g for g in range(m) if g not in Y]
            pool = [g for g in J + [Y[w]] if g in v[x]]
            for H0 in itertools.combinations(pool, 2):
                if v[x][H0[0]] + v[x][H0[1]] <= v[x][Y[x]]: continue
                C['DT1 swaps'] += 1
                bases = [[g] for g in Y]; bases[w] = [Y[x]]; bases[x] = list(H0)
                J2 = [g for g in range(m) if not any(g in b for b in bases)]
                owners = [o for o in range(n) if o not in (x, w)]
                okk = [gdt_completion(O, bases, x, o, J2) for o in owners]
                any1 = O.holds(bases, chain='none', A=1)
                C['every owner works (DT1 conclusion)'] += all(okk)
                C['some owner fails'] += not all(okk)
                C['no owner works'] += not any(okk)
                C['no one-absorber completion after the swap'] += not any1
                if not all(okk) and shown < 4:
                    shown += 1
                    print('DT1 FAILS', json.dumps((sets, vals)), 'order', order, 'picks', Y, 'x', x, 'w', w, 'H0', H0,
                          'owners ok', dict(zip(owners, okk)), 'one-absorber completion', any1, flush=True)
        O.close()
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
