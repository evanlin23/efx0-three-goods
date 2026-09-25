"""Independent brute-force replay of the failed LS4+ designs (attempts/k4-lsp-*.md, k4/ls4plus.md).

Plain Python from the raw EFX0 definition on explicit integer values (helpers from k4/ls4_attempts.py). Levels are
ranks among an agent's subset sums (the representatives are strict types, so ranks are well defined).
Usage: python3 k4/lsp_attempts.py      (exit status 1 if any claim fails)
"""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ls4_attempts import parse, efx0, val, moves, completions, dm_placements, replay

def lev(v, S):
    x = val(v, S)
    return sum(1 for r in range(len(v) + 1) for T in itertools.combinations(v, r) if val(v, T) < x)

def cmoves(vals, Y, U, k):
    """C_k of LS4+: a coalition of exactly k agents re-divides its bundles and the pool, each member taking a set of its
    own goods (possibly empty); the rest keep their bundles; the result is EFX0 and the level sum rises."""
    n, out = len(vals), []
    for co in itertools.combinations(range(n), k):
        pool = set(U).union(*[set(Y[i]) for i in co])
        old = sum(lev(vals[i], Y[i]) for i in co)
        opts = [[frozenset(c) for r in range(len(pool & set(vals[h])) + 1)
                 for c in itertools.combinations(sorted(pool & set(vals[h])), r)] for h in co]
        for choice in itertools.product(*opts):
            if sum(len(Z) for Z in choice) != len(frozenset().union(*choice)): continue
            if sum(lev(vals[h], Z) for h, Z in zip(co, choice)) <= old: continue
            X = [set(b) for b in Y]
            for h, Z in zip(co, choice): X[h] = set(Z)
            if efx0(vals, X): out.append(list(zip(co, choice)))
    return out

def junk_free_states(vals, m):
    n = len(vals)
    opts = [[None] + [i for i in range(n) if g in vals[i]] for g in range(m)]
    for A in itertools.product(*opts):
        Y = [frozenset(g for g in range(m) if A[g] == j) for j in range(n)]
        if efx0(vals, [set(b) for b in Y]): yield Y

def trajectory(s, traj):
    vals = parse(s); m = 1 + max(g for v in vals for g in v)
    ok, Y = replay(vals, traj, m)
    return vals, m, ok, Y

def main():
    bad = 0
    def claim(text, got, want):
        nonlocal bad
        print(f"   {text}: {got} (claim {want})"); bad += got != want
    # 1. early stop (attempts/k4-lsp-early-stop.md)
    s = '[0:5 2:8 5:4 6:6] [0:4 3:2 4:5 5:8] [1:2 2:8 4:5 6:4] [1:6 3:2 5:10 6:7]'
    traj = ['20 0 0 0', '1 0 0 0', '40 0 0 0', '4 0 0 0', '4 8 0 0', '4 1 0 0', '4 10 0 0', '4 20 0 0', '4 20 2 0',
            '4 20 40 0', '4 20 10 0', '4 20 10 8', '4 20 10 2', '4 20 10 40', '4 20 12 40', '4 20 12 48']
    print(f"== stop at the first placement (LS4 -DEARLY), n = 4, m = 7\n   values {s}")
    vals, m, ok, Y = trajectory(s, traj)
    claim(f"{len(traj)} LS4 steps replayed as Pareto moves", ok, True)
    states = [[frozenset()] * 4] + [[frozenset(g for g in range(m) if int(x, 16) >> g & 1) for x in l.split()] for l in traj]
    anyp = [t for t, Z in enumerate(states) if dm_placements(vals, Z, set(range(m)) - set().union(*Z))]
    claim("states on the path with a single-dump or dump-plus-solo placement", anyp, [])
    U = set(range(m)) - set().union(*Y)
    claim(f"completions of the final state {[sorted(b) for b in Y]} U={sorted(U)}", len(completions(vals, Y, U)), 0)
    # 2. bounded coalitions (attempts/k4-lsp-bounded-coalitions.md)
    s = '[0:2 1:4 2:10 3:7] [0:3 2:10 5:2 6:6] [1:4 4:3 5:8 6:6] [3:6 4:3 5:10 6:2]'
    traj = ['1 0 0 0', '2 0 0 0', '8 0 0 0', '4 0 0 0', '4 20 0 0', '4 1 0 0', '4 40 0 0', '4 40 10 0', '4 40 2 0',
            '4 40 20 0', '4 40 20 10', '4 41 20 10', '4 41 20 8', '4 41 20 18']
    print(f"== coalition re-divisions of at most 3 agents (LS4 -DCMOVE=3), n = 4, m = 7\n   values {s}")
    vals, m, ok, Y = trajectory(s, traj)
    U = set(range(m)) - set().union(*Y)
    claim(f"{len(traj)} LS4 steps replayed as Pareto moves", ok, True)
    print(f"   final Y = {[sorted(b) for b in Y]}  U = {sorted(U)}")
    for fam in ['M1', 'R', 'XK']:
        claim(f"improving {fam} moves", len(moves(vals, Y, U, fam)), 0)
    for k in (2, 3):
        claim(f"level-sum-raising re-divisions by {k} agents (C_{k})", len(cmoves(vals, Y, U, k)), 0)
    c4 = cmoves(vals, Y, U, 4)
    print(f"   level-sum-raising re-divisions by all 4 agents: {len(c4)} (claim > 0), e.g. {[(i, sorted(Z)) for i, Z in c4[0]] if c4 else None}")
    bad += not c4
    claim("completions of Y", len(completions(vals, Y, U)), 0)
    # 3. leximin potential (attempts/k4-lsp-leximin.md)
    s = '[0:8 2:10 5:6 6:3] [0:5 3:2 4:4 6:8] [1:1 2:8 4:6 6:4] [1:2 3:3 5:6 6:10]'
    print(f"== leximin of the levels as the potential, n = 4, m = 7 (the profile of Proposition 7)\n   values {s}")
    vals = parse(s); m = 7; best, arg = None, []
    for Y in junk_free_states(vals, m):
        key = sorted(lev(vals[i], Y[i]) for i in range(4))
        if best is None or key > best: best, arg = key, [Y]
        elif key == best: arg.append(Y)
    print(f"   leximin-maximal junk-free EFX0 partial allocations: {[[sorted(b) for b in Y] for Y in arg]} (levels sorted {best})")
    claim("number of leximin-maximal states", len(arg), 1)
    Y = arg[0]; U = set(range(m)) - set().union(*Y)
    claim("it is the dead end of Proposition 7", [sorted(b) for b in Y], [[2], [6], [1, 4], [3, 5]])
    claim("completions of it", len(completions(vals, Y, U)), 0)
    print('ALL CLAIMS CONFIRMED' if not bad else f'{bad} CLAIMS FAILED')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
