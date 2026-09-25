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
      XK: as X, but Z_t may also keep goods of Y_t (the LS4 move X, here with the exact validity rule).
      XK2: XK with cycles of length 2 only.  XK1P: XK in which at most one agent takes pool goods.
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
    elif family in ('X', 'XK', 'XK2', 'XK1P'):
        for L in range(2, (2 if family == 'XK2' else n) + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] != min(cyc): continue
                opts = []
                for t in range(L):
                    h, nx = cyc[t], cyc[(t + 1) % L]
                    pool = set(Y[nx]) | U | (set(Y[h]) if family != 'X' else set())
                    opts.append([Z for Z in subsets(pool & set(vals[h])) if Z & set(Y[nx]) and better(h, Z)])
                for choice in itertools.product(*opts):
                    if family == 'XK1P' and sum(1 for Z in choice if Z & U) > 1: continue
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

def threat(v, B):
    return max(val(v, B - {g}) for g in B) if B else 0

def sources(vals, Y):
    n = len(vals)
    return [s for s in range(n) if all(val(vals[i], Y[s]) <= val(vals[i], Y[i]) for i in range(n) if i != s)]

def ok_at(vals, Y, s, J):
    """Y_s + J threat-free for s: no other agent h has theta_h(Y_s + J) > v_h(Y_h)"""
    B = set(Y[s]) | set(J)
    return all(threat(vals[h], B) <= val(vals[h], Y[h]) for h in range(len(vals)) if h != s)

def dm_placements(vals, Y, U):
    """LS4 Phase 2 (b)/(c): a source s* takes J (goods it does not value), every other pool good goes alone to a
    distinct other source not valuing it; all threat-free.  Returns the list of such placements."""
    S, U, res = sources(vals, Y), sorted(U), []
    for s in S:
        free = [u for u in U if u not in vals[s]]
        for r in range(len(free) + 1):
            for J in itertools.combinations(free, r):
                if not ok_at(vals, Y, s, J): continue
                rest = [u for u in U if u not in J]
                others = [t for t in S if t != s]
                for tgt in itertools.permutations(others, len(rest)):
                    if all(u not in vals[t] and ok_at(vals, Y, t, [u]) for u, t in zip(rest, tgt)):
                        X = [set(b) for b in Y]; X[s] |= set(J)
                        for u, t in zip(rest, tgt): X[t].add(u)
                        res.append(X)
    return res

def clean_rule(vals, Y, U):
    """the value-free Phase 2 of attempts/k4-ls-clean-placement.md: s is clean for u if s is a source not valuing u
    and no unsatisfied valuer h != s of u (v_h(Y_h) < v_h(R_h - Y_h)) has a good in Y_s; goods with no clean source
    ('dirty') go alone to distinct sources where they are threat-free, clean goods to clean sources not so used."""
    n, S = len(vals), sources(vals, Y)
    sat = [val(vals[h], Y[h]) >= val(vals[h], set(vals[h]) - Y[h]) for h in range(n)]
    clean = lambda s, u: u not in vals[s] and not any(h != s and u in vals[h] and set(Y[s]) & set(vals[h]) and not sat[h] for h in range(n))
    dirty = [u for u in sorted(U) if not any(clean(s, u) for s in S)]
    for tgt in itertools.permutations(S, len(dirty)):
        if not all(u not in vals[t] and ok_at(vals, Y, t, [u]) for u, t in zip(dirty, tgt)): continue
        if all(any(clean(s, u) and s not in tgt for s in S) for u in U if u not in dirty): return True
    return False

def simple_split(vals, Y, U):
    """the simplest polynomial split: the dump s* keeps every pool good that is individually harmless there, the
    rest is matched alone to other sources"""
    S = sources(vals, Y)
    for s in S:
        J = [u for u in sorted(U) if u not in vals[s] and ok_at(vals, Y, s, [u])]
        if not ok_at(vals, Y, s, J): continue
        rest, others = [u for u in U if u not in J], [t for t in S if t != s]
        for tgt in itertools.permutations(others, len(rest)):
            if all(u not in vals[t] and ok_at(vals, Y, t, [u]) for u, t in zip(rest, tgt)): return True
    return False

def replay(vals, traj, m):
    """each step of a trajectory (hex masks) must be a Pareto move: the agents whose bundle changed strictly gain,
    the others keep their bundles, the state is junk-free and EFX0"""
    n, prev, ok = len(vals), [frozenset() for _ in vals], True
    for line in traj:
        Y = [frozenset(g for g in range(m) if int(x, 16) >> g & 1) for x in line.split()]
        movers = [i for i in range(n) if Y[i] != prev[i]]
        ok &= bool(movers) and all(val(vals[i], Y[i]) > val(vals[i], prev[i]) for i in movers)
        ok &= efx0(vals, [set(b) for b in Y]) and all(g in vals[i] for i in range(n) for g in Y[i])
        prev = Y
    return ok, prev

EXTRA = [
    # name, values, Y, U, families with no move, families with a move, extra claims
    ('exchange cycles of length <= 2 (attempts/k4-ls-short-cycles.md), n = 3, m = 5',
     '[0:1 1:4 2:6 4:8] [1:2 3:3 4:4] [2:3 3:4 4:2]', [{4}, {3}, {2}], {0, 1}, ['M1', 'R', 'XK2'], ['XK'], ['no_completion']),
    ('at most one pool-using agent per cycle (attempts/k4-ls-one-pool-agent.md), n = 5, m = 8',
     '[0:2 2:4 6:7 7:8] [1:3 2:2 5:4] [1:3 6:2 7:4] [3:2 4:3 5:4] [3:2 4:8 6:5 7:4]', [{7}, {5}, {1}, {4}, {3, 6}], {0, 2},
     ['M1', 'R', 'XK1P'], ['XK'], ['no_completion']),
    ('clean placement ignoring values (attempts/k4-ls-clean-placement.md), n = 3, m = 5',
     '[0:1 2:8 3:6 4:4] [1:2 2:4 3:10 4:7] [2:4 3:3 4:2]', [{2}, {3}, {4}], {0, 1}, ['M1', 'R', 'XK'], [],
     ['clean_rule_fails', 'dm_exists']),
    ('simplest polynomial split (attempts/k4-ls-simple-split.md), n = 4, m = 6',
     '[0:1 1:6 3:8 4:4] [1:3 2:2 5:4] [2:5 3:3 4:6 5:7] [2:7 3:10 4:4 5:2]', [{3}, {5}, {4}, {2}], {0, 1}, ['M1', 'R', 'XK'], [],
     ['no_single_dump', 'simple_split_fails', 'dm_exists']),
]
ALT = ('choice rule -DALT (attempts/k4-ls-alt-rule.md), n = 4, m = 7',
       '[0:3 1:6 2:10 3:8] [0:2 2:8 5:4 6:3] [1:4 4:2 5:5 6:8] [3:4 4:3 5:2 6:8]',
       ['4 0 0 0', '4 20 0 0', '4 20 40 0', '4 20 40 18', '4 21 40 18'])

def extra_checks():
    bad = 0
    for name, s, Y, U, none_fam, some_fam, claims in EXTRA:
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
        for c in claims:
            if c == 'no_completion':
                k = len(completions(vals, Y, U)); print(f"   completions (pool goods anywhere): {k} (claim 0)"); bad += k != 0
            if c == 'no_single_dump':
                k = len(single_dump(vals, Y, U)); print(f"   single-dump completions: {k} (claim 0)"); bad += k != 0
            if c == 'clean_rule_fails':
                r = clean_rule(vals, Y, U); print(f"   clean placement rule succeeds: {r} (claim False)"); bad += r
            if c == 'simple_split_fails':
                r = simple_split(vals, Y, U); print(f"   simplest split succeeds: {r} (claim False)"); bad += r
            if c == 'dm_exists':
                d = dm_placements(vals, Y, U)
                print(f"   dump-plus-solo placements (LS4 Phase 2 (b)/(c)): {[[sorted(b) for b in X] for X in d[:2]]} ({len(d)}; claim > 0)")
                bad += not d or not all(efx0(vals, X) for X in d)
    name, s, traj = ALT
    vals = parse(s); m = 1 + max(g for v in vals for g in v)
    print(f"== {name}\n   values {s}")
    ok, Y = replay(vals, traj, m); U = set(range(m)) - set().union(*Y)
    print(f"   {len(traj)} steps replayed, each a Pareto move keeping junk-free EFX0: {ok}"); bad += not ok
    print(f"   final Y = {[sorted(b) for b in Y]}  U = {sorted(U)}")
    for fam in ['M1', 'R', 'XK']:
        k = len(moves(vals, Y, U, fam)); print(f"   improving {fam} moves: {k} (claim 0)"); bad += k != 0
    k = len(completions(vals, Y, U)); print(f"   completions (pool goods anywhere): {k} (claim 0)"); bad += k != 0
    k = len(moves(vals, Y, U, 'G')); print(f"   coalition moves: {k} (so not a dead end: a Pareto continuation exists)")
    return bad

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
    bad = dead_end_check() + extra_checks()
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
