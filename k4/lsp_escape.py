"""Escape study of k4/ls4plus.md §1: plain-Python replay over the 19 logged LS4 failure states.

Input: results/k4_ls4_failures_4_pure.tsv (profile, final state Y and pool U, LS4's trajectory, and the state right after
the coalition move of LS4+_n). Everything below is brute force from the raw EFX0 definition on the explicit integer
values (helpers from k4/ls4_attempts.py); levels are ranks among an agent's subset sums (strict types).
For each row it reports:
  - whether Y is a dead end (no complete EFX0 allocation gives every agent at least its value in Y);
  - the minimum number of worse-off agents over complete EFX0 allocations, and which agents can be the only loser;
  - for non-dead Y: how many agents' valued bundles change in the complete EFX0 allocations dominating Y;
  - the smallest level-sum-raising re-division (junk-free EFX0 Z with larger level sum, fewest changed agents), with
    its loser count; for dead ends also the smallest one reaching a non-dead Z;
  - for dead ends: the first dead state on LS4's trajectory (each step also replayed as a Pareto move);
  - the coalition move LS4+_n applies: its size, losers, and whether it is EFX0 and raises the level sum.
Then it checks the summary claims of k4/ls4plus.md §1. Usage: python3 k4/lsp_escape.py  (exit 1 if a claim fails)
"""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ls4_attempts import parse, efx0, val, replay

def lev(v, S):
    x = val(v, S)
    return sum(1 for r in range(len(v) + 1) for T in itertools.combinations(v, r) if val(v, T) < x)

def dec(x, m): return frozenset(g for g in range(m) if int(x, 16) >> g & 1)

def main():
    rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(HERE, '..', 'results', 'k4_ls4_failures_4_pure.tsv'))
            if l.strip() and not l.startswith('#') and not l.startswith('m\t')]
    summ = []
    for r, (mm, s, Ym, Um, traj, cst) in enumerate(rows, 1):
        m, vals = int(mm), parse(s); n = len(vals)
        Y = [dec(x, m) for x in Ym.split()]; lY = [lev(vals[i], Y[i]) for i in range(n)]
        comp = []                                   # complete EFX0 allocations: (levels of valued parts, valued parts)
        for A in itertools.product(range(n), repeat=m):
            X = [frozenset(g for g in range(m) if A[g] == j) for j in range(n)]
            if efx0(vals, [set(b) for b in X]):
                XR = [X[i] & frozenset(vals[i]) for i in range(n)]
                comp.append(([lev(vals[i], XR[i]) for i in range(n)], XR))
        dom = [XR for l, XR in comp if all(a >= b for a, b in zip(l, lY))]
        dead = not dom
        worse = [[i for i in range(n) if l[i] < lY[i]] for l, _ in comp]
        minw = min(len(w) for w in worse)
        sole = sorted({w[0] for w in worse if len(w) == 1})
        psizes = sorted({sum(1 for i in range(n) if XR[i] != Y[i]) for XR in dom})
        def alive(lz): return any(all(a >= b for a, b in zip(l, lz)) for l, _ in comp)
        opts = [[None] + [i for i in range(n) if g in vals[i]] for g in range(m)]
        best, best_alive = {}, {}
        for A in itertools.product(*opts):
            Z = [frozenset(g for g in range(m) if A[g] == j) for j in range(n)]
            lz = [lev(vals[i], Z[i]) for i in range(n)]
            if sum(lz) <= sum(lY) or not efx0(vals, [set(b) for b in Z]): continue
            ch = sum(1 for i in range(n) if Z[i] != Y[i]); lo = sum(1 for i in range(n) if lz[i] < lY[i])
            best[ch] = min(best.get(ch, 9), lo)
            if dead and alive(lz): best_alive[ch] = min(best_alive.get(ch, 9), lo)
        k = min(best); ka = min(best_alive) if best_alive else None
        ok, last = replay(vals, traj.split(','), m)
        path = [[dec(x, m) for x in st.split()] for st in traj.split(',')]
        firstdead = next((t + 1 for t, Z in enumerate(path) if not alive([lev(vals[i], Z[i]) for i in range(n)])), None)
        C = [dec(x, m) for x in cst.split()]; lC = [lev(vals[i], C[i]) for i in range(n)]
        c_ok = efx0(vals, [set(b) for b in C]) and all(g in vals[i] for i in range(n) for g in C[i]) and sum(lC) > sum(lY)
        c_size = sum(1 for i in range(n) if C[i] != Y[i]); c_los = [i for i in range(n) if lC[i] < lY[i]]
        print(f"row {r:2d} m={m} {'DEAD ' if dead else 'alive'} min-worse={minw} sole-losers={sole} "
              f"pareto-sizes={psizes or '-'} smallest-raise={k}({best[k]} losers) "
              f"smallest-raise-to-alive={ka if ka is None else f'{ka}({best_alive[ka]} losers)'} "
              f"path-ok={ok and last == Y} first-dead-step={firstdead}/{len(path)} "
              f"LS4+move: valid={c_ok} size={c_size} losers={c_los}", flush=True)
        summ.append(dict(dead=dead, minw=minw, sole=sole, psizes=psizes, k=k, klos=best[k], ka=ka,
                         kalos=best_alive.get(ka), ok=ok and last == Y, fd=firstdead, T=len(path),
                         c_ok=c_ok, c_size=c_size, c_los=c_los))
    bad = 0
    def claim(text, got, want):
        nonlocal bad
        print(f"  {text}: {got} (claim {want})"); bad += got != want
    D = [x for x in summ if x['dead']]; A = [x for x in summ if not x['dead']]
    print("summary")
    claim("dead ends / not dead", (len(D), len(A)), (8, 11))
    claim("every trajectory replays as Pareto moves ending at Y", all(x['ok'] for x in summ), True)
    claim("dead ends: minimum number of worse-off agents", sorted({x['minw'] for x in D}), [1])
    claim("dead ends: agent 3 can be the only worse-off agent", all(3 in x['sole'] for x in D), True)
    claim("dead ends: first dead state is LS4's last state", all(x['fd'] == x['T'] for x in D), True)
    claim("dead ends: smallest raise reaching a non-dead state, sizes", sorted(x['ka'] for x in D), [2] * 7 + [3])
    claim("dead ends: ... with exactly one loser", sorted({x['kalos'] for x in D}), [1])
    claim("not dead: every dominating complete allocation changes all 4 valued bundles", all(x['psizes'] == [4] for x in A), True)
    claim("not dead: smallest level-sum-raising re-division, rows by size",
          {k: [r for r, x in enumerate(summ, 1) if not x['dead'] and x['k'] == k] for k in (2, 3, 4)},
          {2: [1, 4, 7, 11, 13, 18], 3: [3, 12, 15], 4: [2, 5]})
    claim("not dead: fewest losers among the smallest re-divisions, where they have 2 or 3 agents",
          sorted({x['klos'] for x in A if x['k'] < 4}), [1])
    claim("not dead: fewest losers among the 4-agent re-divisions of rows 2 and 5 (Pareto ones exist)",
          [x['klos'] for x in A if x['k'] == 4], [0, 0])
    claim("LS4+_n's coalition move is valid (junk-free, EFX0, level sum up) at all 19", all(x['c_ok'] for x in summ), True)
    claim("LS4+_n's coalition move has exactly one loser at all 19", all(len(x['c_los']) == 1 for x in summ), True)
    claim("LS4+_n's coalition move sizes (2, 3, 4)", tuple(sum(1 for x in summ if x['c_size'] == k) for k in (2, 3, 4)), (13, 4, 2))
    claim("dead ends: the loser of LS4+_n's move is never agent 3", all(3 not in x['c_los'] for x in D), True)
    print('ALL CLAIMS CONFIRMED' if not bad else f'{bad} CLAIMS FAILED')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
