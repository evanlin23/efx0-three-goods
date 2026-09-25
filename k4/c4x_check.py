#!/usr/bin/env python3
"""Independent checker for k4/c4x.c, written from the definitions (k4/lb4.md §1, lean/EFX/PreAllocK.lean).

It shares no code with c4x.c. For a profile it enumerates
- every base map: each good goes to nobody (junk) or to one agent that values it, each agent at most 2 goods;
- needs N_i = {g in R_i \\ B_i : v_i(g) > v_i(B_i)} (value-based); validity (V1), (V2) literally;
- every completion literally as Lean's `Completion` with the owner's needs from its bundle (`ownerNeeds`):
  owner None or any agent, every map of the junk to agents; conditions: the owner is not frozen, a frozen agent
  other than the owner gets no junk, a free agent j != owner gets at most 2 - |B_j| junk goods, validity with the
  owner's needs replaced, and (OC4) v_j(X_o \\ h) <= v_j(X_j) for all j != o, h in X_o;
- as a sanity check of Theorem 1'4, every completion found is re-checked to be EFX0 from the raw definition;
and reports per profile: #valid P, #completable P, and for each potential of POTS whether every maximum / some
maximum is completable.

usage: python3 k4/c4x_check.py FILE CORE_INDEX [--rand=N --seed=S | --all] [--w0]
  prints one line per profile: PROF t_0 .. t_{n-1} nvalid ncompl  every/some flags per potential."""
import gzip, json, sys, itertools, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check4 import core_domains

POTS = ['sumlev', 'leximin', 'leximax', '-frozen', '(-frozen,sumlev)', '(-frozen,leximin)', '(-frozen,-rodef)', '(-frozen,slots)']
# the same potentials as c4x.c feature lists (for the cross-check): c4x -R -p C_POTS
C_POTS = '0;3;2;6;6,0;6,3;6,17;6,8'

def val(vals, S):
    return sum(vals.get(g, 0) for g in S)

def efx0(vals_list, X, n):
    for i in range(n):
        for j in range(n):
            if i == j: continue
            for h in X[j]:
                if val(vals_list[i], X[j] - {h}) > val(vals_list[i], X[i]): return False
    return True

def analyse(sets, m, vals_list, w0=False, ef=False, big=False):
    """All valid pre-allocations with their completability and potentials. Variants: w0 (the owner's needs from its
    base), ef (bases of two or more goods must be envy-free: v(B) >= v(R \\ B)), big (one base may have 3 or 4 goods;
    a completion must then make its agent the owner, which Lean's Completion already forces)."""
    n = len(sets)
    R = [set(S) for S in sets]
    choices = [[None] + [i for i in range(n) if g in R[i]] for g in range(m)]
    results = []   # (bases, completable, feats)
    for bm in itertools.product(*choices):
        B = [frozenset(g for g in range(m) if bm[g] == i) for i in range(n)]
        if big:
            if sum(len(b) > 2 for b in B) > 1: continue
        elif any(len(b) > 2 for b in B): continue
        if ef and any(len(B[i]) >= 2 and 2 * val(vals_list[i], B[i]) < val(vals_list[i], R[i]) for i in range(n)): continue
        J = frozenset(g for g in range(m) if bm[g] is None)
        N = [frozenset(g for g in R[i] - B[i] if vals_list[i][g] > val(vals_list[i], B[i])) for i in range(n)]
        NA = frozenset().union(*N)
        if J & NA: continue                                              # (V1)
        if any(len(B[i]) >= 2 and B[i] & NA for i in range(n)): continue  # (V2)
        comp = completable(n, m, R, vals_list, B, J, N, w0)
        frozen = [len(B[i]) == 1 and B[i] <= NA for i in range(n)]
        cap = [0 if frozen[i] else max(0, 2 - len(B[i])) for i in range(n)]
        lev = [sum(1 for T in range(1 << len(sets[i])) if sum(vals_list[i][sets[i][k]] for k in range(len(sets[i])) if T >> k & 1) < val(vals_list[i], B[i])) for i in range(n)]
        feats = {
            'sumlev': sum(lev),
            'leximin': tuple(sorted(lev)),
            'leximax': tuple(sorted(lev, reverse=True)),
            '-frozen': -sum(frozen),
            '(-frozen,sumlev)': (-sum(frozen), sum(lev)),
            '(-frozen,leximin)': (-sum(frozen), tuple(sorted(lev))),
            '(-frozen,slots)': (-sum(frozen), sum(cap)),
            'rodef': rodef(n, vals_list, B, J, frozen, cap, R, N, w0),
        }
        results.append((B, comp, feats))
    mf = max(r[2]['-frozen'] for r in results)
    for r in results:
        r[2]['(-frozen,-rodef)'] = (r[2]['-frozen'], -r[2]['rodef'] if r[2]['-frozen'] == mf else -1000)
    return results

def threatened(vals, X, Bx):
    return any(val(vals, X - {h}) > val(vals, Bx) for h in X)

def rodef(n, vals_list, B, J, frozen, cap, R, N, w0=False):
    """Removal-only deficit: |J| - S if |J| <= S; else the least, over the free owners o and the sets C ⊆ J such
    that X_o = B_o ∪ (J \\ C) threatens no agent x != o holding its base, of |C| - S_o(C), where S_o(C) counts the
    slots of the agents other than o with frozen status from the owner's needs taken from X_o (w0: from B_o)."""
    S = sum(cap)
    if len(J) <= S: return len(J) - S
    best = None
    Jl = sorted(J)
    for o in range(n):
        if frozen[o]: continue
        for r in range(len(Jl) + 1):
            for C in itertools.combinations(Jl, r):
                X = set(B[o]) | (set(J) - set(C))
                if any(threatened(vals_list[x], X, B[x]) for x in range(n) if x != o): continue
                if w0: No = N[o]
                else: No = frozenset(g for g in R[o] - X if vals_list[o][g] > val(vals_list[o], X))
                NAp = frozenset().union(*[N[j] for j in range(n) if j != o]) | No
                So = sum(0 if (len(B[j]) == 1 and B[j] <= NAp) else 2 - len(B[j]) for j in range(n) if j != o)
                d = r - So
                if best is None or d < best: best = d
    return best if best is not None else 1 << 20

def completable(n, m, R, vals_list, B, J, N, w0):
    Jl = sorted(J)
    for o in [None] + list(range(n)):
        for jm in itertools.product(range(n), repeat=len(Jl)):
            X = [set(B[i]) for i in range(n)]
            for g, a in zip(Jl, jm): X[a].add(g)
            if o is None:
                Np = N
            else:
                if w0: Np = N
                else: Np = [frozenset(g for g in R[o] - X[o] if vals_list[o][g] > val(vals_list[o], X[o])) if i == o else N[i] for i in range(n)]
            NAp = frozenset().union(*Np)
            if J & NAp: continue
            if any(len(B[i]) >= 2 and B[i] & NAp for i in range(n)): continue
            frozen = [len(B[i]) == 1 and B[i] <= NAp for i in range(n)]
            ok = True
            if o is not None and frozen[o]: ok = False
            for j in range(n):
                if not ok: break
                if j == o: continue
                Cj = X[j] - B[j]
                if frozen[j] and Cj: ok = False
                if not frozen[j] and len(Cj) + len(B[j]) > 2: ok = False
            if not ok: continue
            if o is not None:
                for j in range(n):
                    if j == o: continue
                    if any(val(vals_list[j], X[o] - {h}) > val(vals_list[j], X[j]) for h in X[o]): ok = False; break
            if not ok: continue
            assert efx0(vals_list, [frozenset(x) for x in X], n), (B, X)
            big = sum(len(x) > 2 for x in X)
            assert big <= 1
            return True
    return False

def main():
    f, ci = sys.argv[1], int(sys.argv[2])
    rand, seed, w0, allp = 0, 1, False, False
    for a in sys.argv[3:]:
        if a.startswith('--rand='): rand = int(a[7:])
        elif a.startswith('--seed='): seed = int(a[7:])
        elif a == '--w0': w0 = True
        elif a == '--all': allp = True
    data = json.load(gzip.open(f, 'rt'))
    core = data['cores'][ci]
    n, m, sets = core['n'], core['m'], core['sets']
    doms = core_domains(sets, m, False)
    if allp: profs = itertools.product(*[range(len(D)) for D in doms])
    else:
        rng = random.Random(seed)
        profs = [tuple(rng.randrange(len(D)) for D in doms) for _ in range(rand)]
    for ts in profs:
        vals_list = [doms[i][ts[i]] for i in range(n)]
        res = analyse(sets, m, vals_list, w0)
        flags = []
        for p in POTS:
            best = max(r[2][p] for r in res)
            mx = [r for r in res if r[2][p] == best]
            flags.append(f'{int(all(r[1] for r in mx))}{int(any(r[1] for r in mx))}')
        print('PROF', *ts, len(res), sum(r[1] for r in res), *flags)
        sys.stdout.flush()

if __name__ == '__main__':
    main()
