"""Independent brute-force replay of the failing configurations of rejected LS4 variants (attempts/k4-ls-*.md).

Written separately from ls4.c / ls4alg.c: plain Python, raw EFX0 definition on the explicit integer values, every move
family enumerated by brute force.  For each example it checks that the stated state Y (junk-free partial allocation,
pool U) is EFX0, lists which move families improve it, and decides the completion questions by trying every
assignment of the pool goods.
Usage: python3 k4/ls4_attempts.py            (all examples; exit status 1 if any claim fails)
"""
import itertools, sys

def parse(s):
    return [{int(a): int(b) for a, b in (x.split(':') for x in part.strip('[] ').split())} for part in s.strip().split('] [')]

def val(v, S): return sum(v.get(g, 0) for g in S)

def efx0(vals, X):
    """raw definition: v_i(X_i) >= v_i(X_j) - v_i(h) for all i != j, h in X_j (the pool is not a bundle)"""
    n = len(vals)
    return all(val(vals[i], X[i]) >= val(vals[i], X[j]) - vals[i].get(h, 0)
               for i in range(n) for j in range(n) if j != i for h in X[j])

def subsets(S):
    S = sorted(S)
    for r in range(len(S) + 1):
        for c in itertools.combinations(S, r): yield frozenset(c)

def moves(vals, Y, U, family):
    """All improving moves of a family; each move is a list of (agent, new bundle); movers strictly better, others
    keep their bundles, new bundles of movers consist of goods they value, result EFX0.
      M1: one agent, Z subset of (Y_h | U).
      R: envy cycle, each takes the successor's bundle.
      X: cycle of >= 2 distinct agents, Z_t subset of (Y_succ | U), meets Y_succ, disjoint.
      XK: as X, but Z_t may also keep goods of Y_t (the LS4 move; plus 'local': Z_t threat-free for old values).
      G: any coalition of >= 2 agents re-dividing their bundles and U."""
    n = len(vals); out = []
    def ok(assign):
        X = [set(Y[i]) for i in range(n)]
        for i, Z in assign: X[i] = set(Z)
        used = [g for _, Z in assign for g in Z]
        if len(used) != len(set(used)): return False
        return efx0(vals, X)
    better = lambda i, Z: all(g in vals[i] for g in Z) and val(vals[i], Z) > val(vals[i], Y[i])
    if family == 'M1':
        for h in range(n):
            for Z in subsets((set(Y[h]) | U) & set(vals[h])):
                if better(h, Z) and ok([(h, Z)]): out.append([(h, Z)])
    elif family == 'R':
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] != min(cyc): continue
                if all(val(vals[cyc[t]], Y[cyc[(t + 1) % L]]) > val(vals[cyc[t]], Y[cyc[t]]) for t in range(L)):
                    out.append([(cyc[t], frozenset(Y[cyc[(t + 1) % L]])) for t in range(L)])
    elif family in ('X', 'XK'):
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] != min(cyc): continue
                opts = []
                for t in range(L):
                    h, nx = cyc[t], cyc[(t + 1) % L]
                    pool = set(Y[nx]) | U | (set(Y[h]) if family == 'XK' else set())
                    opts.append([Z for Z in subsets(pool & set(vals[h])) if Z & set(Y[nx]) and better(h, Z)])
                for choice in itertools.product(*opts):
                    a = list(zip(cyc, choice))
                    if ok(a): out.append(a)
    elif family == 'G':
        for L in range(2, n + 1):
            for co in itertools.combinations(range(n), L):
                pool = set(U).union(*[set(Y[i]) for i in co])
                opts = [[Z for Z in subsets(pool & set(vals[h])) if better(h, Z)] for h in co]
                for choice in itertools.product(*opts):
                    a = list(zip(co, choice))
                    if ok(a): out.append(a)
    return out

def completions(vals, Y, U, junk_only=False):
    """all complete EFX0 allocations extending Y by the goods of U (junk_only: each pool good to an agent not valuing it)"""
    n, U = len(vals), sorted(U); res = []
    for A in itertools.product(range(n), repeat=len(U)):
        if junk_only and any(u in vals[i] for u, i in zip(U, A)): continue
        X = [set(Y[i]) for i in range(n)]
        for u, i in zip(U, A): X[i].add(u)
        if efx0(vals, X): res.append(X)
    return res

def single_dump(vals, Y, U):
    """complete EFX0 allocations that add all of U to ONE bundle"""
    res = []
    for i in range(len(vals)):
        X = [set(b) for b in Y]; X[i] |= U
        if efx0(vals, X): res.append(X)
    return res

EXAMPLES = [
    # (name, values, Y, U, families that must have NO move, families that must have a move, claim)
    ('M1+R only (attempts/k4-ls-no-exchange.md), n = 2, m = 4',
     '[0:4 1:1 2:6 3:8] [0:2 1:3 2:4 3:8]', [{3}, {1, 2}], {0}, ['M1', 'R'], ['X'], 'no_completion'),
    ('exchange cycles without keep, champion cycles included (attempts/k4-ls-exchange-no-keep.md), n = 3, m = 6',
     '[0:6 1:4 2:8 5:5] [1:4 3:8 4:2 5:5] [2:6 3:10 4:3 5:2]', [{0, 5}, {3}, {2, 4}], {1}, ['M1', 'R', 'X'], ['XK'],
     'no_completion'),
    ('single dump (attempts/k4-ls-single-dump.md), n = 4, m = 7',
     '[0:1 2:6 5:4 6:8] [1:4 2:6 3:8 4:1] [1:7 4:2 5:6 6:10] [3:10 4:4 5:7 6:2]', [{6}, {3}, {1, 4}, {5}], {0, 2},
     ['M1', 'R', 'XK', 'G'], [], 'no_single_dump'),
]

DEAD_END = ('LS4 dead end (attempts/k4-ls-dead-end.md), n = 4, m = 7',
            '[0:8 2:10 5:6 6:3] [0:5 3:2 4:4 6:8] [1:1 2:8 4:6 6:4] [1:2 3:3 5:6 6:10]',
            # LS4's trajectory from the empty allocation (bundles as bit masks, as printed by ls4alg.c -DTRACE)
            ['40 0 0 0', '20 0 0 0', '1 0 0 0', '4 0 0 0', '4 8 0 0', '4 10 0 0', '4 1 0 0', '4 40 0 0', '4 40 2 0',
             '4 40 10 0', '4 40 10 2', '4 40 10 8', '4 40 12 8', '4 40 12 20', '4 40 12 28'])

def dead_end_check():
    name, s, traj = DEAD_END
    vals = parse(s); n, m = len(vals), 1 + max(g for v in vals for g in v); bad = 0
    print(f"== {name}\n   values {s}")
    prev = [frozenset() for _ in range(n)]
    for k, line in enumerate(traj, 1):
        Y = [frozenset(g for g in range(m) if int(x, 16) >> g & 1) for x in line.split()]
        U = set(range(m)) - set().union(*Y)
        movers = [i for i in range(n) if Y[i] != prev[i]]
        ok = (efx0(vals, [set(b) for b in Y]) and all(g in vals[i] for i in range(n) for g in Y[i])
              and len(movers) == 1 and val(vals[movers[0]], Y[movers[0]]) > val(vals[movers[0]], prev[movers[0]])
              and Y[movers[0]] <= prev[movers[0]] | (set(range(m)) - set().union(*prev)))
        if not ok: print(f"   step {k} is not a valid single-agent rebundle (M1): {[sorted(b) for b in Y]}"); bad += 1
        prev = Y
    print(f"   {len(traj)} steps replayed, each a valid M1 move (one agent takes goods from its bundle and the pool, "
          f"strictly better, junk-free, EFX0): {not bad}")
    Y, U = prev, set(range(m)) - set().union(*prev)
    print(f"   final Y = {[sorted(b) for b in Y]}  U = {sorted(U)}  values {[val(vals[i], Y[i]) for i in range(n)]}")
    for fam in ['M1', 'R', 'XK', 'G']:
        k = len(moves(vals, Y, U, fam)); print(f"   improving {fam} moves: {k} (claim 0)"); bad += k != 0
    c = completions(vals, Y, U); print(f"   completions of Y: {len(c)} (claim 0)"); bad += len(c) != 0
    dom = 0
    for A in itertools.product(range(n), repeat=m):
        X = [{g for g in range(m) if A[g] == j} for j in range(n)]
        if all(val(vals[i], X[i]) >= val(vals[i], Y[i]) for i in range(n)) and efx0(vals, X): dom += 1
    print(f"   complete EFX0 allocations in which every agent gets at least its value in Y: {dom} of {n ** m} checked (claim 0)")
    bad += dom != 0
    return bad

def main():
    bad = dead_end_check()
    for name, s, Y, U, none_fam, some_fam, claim in EXAMPLES:
        vals = parse(s); Y = [frozenset(b) for b in Y]
        print(f"== {name}\n   values {s}\n   Y = {[sorted(b) for b in Y]}  U = {sorted(U)}")
        ok = efx0(vals, [set(b) for b in Y]) and all(g in vals[i] for i in range(len(Y)) for g in Y[i])
        print(f"   Y junk-free and EFX0: {ok}"); bad += not ok
        for fam in none_fam:
            k = len(moves(vals, Y, U, fam)); print(f"   improving {fam} moves: {k} (claim 0)"); bad += k != 0
        for fam in some_fam:
            mv = moves(vals, Y, U, fam)
            print(f"   improving {fam} moves: {len(mv)} (claim > 0), e.g. {[(i, sorted(Z)) for i, Z in mv[0]] if mv else None}")
            bad += not mv
        if claim == 'no_completion':
            c = completions(vals, Y, U)
            print(f"   complete EFX0 allocations extending Y (pool goods anywhere): {len(c)} (claim 0)"); bad += len(c) != 0
        else:
            c1, c = single_dump(vals, Y, U), completions(vals, Y, U, junk_only=True)
            print(f"   single-dump completions: {len(c1)} (claim 0); junk completions: {[[sorted(b) for b in X] for X in c]}")
            bad += len(c1) != 0 or not c
            n, m = len(vals), 1 + max(g for v in vals for g in v)
            dom = []
            for A in itertools.product(range(n), repeat=m):
                X = [{g for g in range(m) if A[g] == j} for j in range(n)]
                if all(val(vals[i], X[i]) >= val(vals[i], Y[i]) for i in range(n)) and efx0(vals, X): dom.append(X)
            print(f"   complete EFX0 allocations weakly better than Y for every agent: {[[sorted(b) for b in X] for X in dom]}")
    print('ALL CLAIMS CONFIRMED' if not bad else f'{bad} CLAIMS FAILED')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
