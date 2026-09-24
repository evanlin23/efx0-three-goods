"""Cross-check (evidence, not proof): the Lean definition `EFX.LB.lb` (lean/EFX/LBRun.lean) computes the same
allocation as src/construct.py on every ranking profile of the given connected cores.

The Lean `lb` takes Phase 1's processing order as an input (LB chooses it adaptively). For each (core, profile) this
script records the order in which construct.phase1 processes the agents (a copy of its loop that also records the
order; its picks are checked against construct.phase1's), then runs the Lean `lb` with that order and compares its
allocation with construct.construct (or both fail). Goods and agents are Nat in Lean (the list layer is generic).

Usage (from the repository root, after `cd lean && lake build`):
  python lean/scripts/lb_crosscheck.py N [N ...] [--every=K]    # all connected cores with N agents, every m;
                                                                # every K-th profile (default 1: all)
"""
import itertools, os, subprocess, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'src'))
import construct
from cores_nauty import gen_cores_nauty

def phase1_order(n, m, trip):
    """construct.phase1, recording the processing order."""
    R = [set(t) for t in trip]
    rank = [{g: r for r, g in enumerate(t)} for t in trip]
    order = []
    def r1_step(A, G, Y, rec):
        best = None
        for i in sorted(A):
            left = R[i] & G
            if len(left) <= 2:
                fav = min(left, key=lambda g: rank[i][g]) if left else None
                key = (rank[i][fav] if left else 3, len(left), i)
                if best is None or key < best[0]: best = (key, i, fav)
        if best is None: return False
        _, i, fav = best
        Y[i] = fav; A.discard(i); G.discard(fav)
        if rec is not None: rec.append(i)
        return True
    def na_count(A, G, Y):
        done = [k for k in range(n) if k not in A]
        held = {k: rank[k][Y[k]] if Y[k] is not None else 3 for k in done}
        junk = {g for g in G if not any(g in R[k] for k in A)}
        up = set()
        while True:
            NA = {g for k in done if k not in up for g in trip[k][:held[k]]}
            k = next((k for k in done if k not in up and held[k] == 1 and trip[k][2] in junk and trip[k][1] not in NA), None)
            if k is None: return len(NA)
            up.add(k); junk.discard(trip[k][2])
    A, G, Y = set(range(n)), set(range(m)), [None] * n
    while A:
        if r1_step(A, G, Y, order): continue
        best = None
        for i in sorted(A):
            A2, G2, Y2 = set(A), set(G), list(Y)
            Y2[i] = trip[i][0]; A2.discard(i); G2.discard(trip[i][0])
            while A2 and r1_step(A2, G2, Y2, None): pass
            key = (na_count(A2, G2, Y2), i)
            if best is None or key < best[0]: best = (key, i)
        i = best[1]
        Y[i] = trip[i][0]; A.discard(i); G.discard(trip[i][0]); order.append(i)
    return Y, order

RUNNER = r'''
import EFX.LBRun
open EFX LB

def nats (s : String) : List Nat := (s.splitOn " ").filterMap String.toNat?

/-- `lb` on agents `0..n-1`, goods `0..m-1`, profile `trip`, Phase 1 order `order`: the owner of each good,
or `none` if LB fails. -/
def runLB (n m : Nat) (trip order : List Nat) : Option (List Nat) :=
  let P : Profile Nat Nat := ⟨fun i => trip.getD (3 * i) 0, fun i => trip.getD (3 * i + 1) 0,
    fun i => trip.getD (3 * i + 2) 0⟩
  (lb P (List.range n) (List.range m) order 0).map (fun X => (List.range m).map X)

def main (args : List String) : IO UInt32 := do
  let lines ← IO.FS.lines (args.getD 0 "")
  let mut bad := 0
  for line in lines do
    match line.splitOn "|" with
    | [nm, t, o, x] =>
      let nm := nats nm
      let got := runLB (nm.getD 0 0) (nm.getD 1 0) (nats t) (nats o)
      let want := if x == "-" then none else some (nats x)
      if got != want then
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"MISMATCH {line}: lean {got}"
    | _ => IO.println s!"bad line {line}"; return 2
  IO.println s!"{lines.size} cases, {bad} mismatches"
  return (if bad == 0 then 0 else 1)
'''

def main():
    ns = [int(a) for a in sys.argv[1:] if not a.startswith('--')]
    every = next((int(a.split('=')[1]) for a in sys.argv[1:] if a.startswith('--every=')), 1)
    lines, large, fails = [], 0, 0
    for n in ns:
        for m in range(3, 2 * n + 1):
            for _, sets in gen_cores_nauty(n, m):
                for t, prof in enumerate(itertools.product(range(6), repeat=n)):
                    if t % every: continue
                    trip = [tuple(S[p] for p in construct.PERMS[k]) for S, k in zip(sets, prof)]
                    Y, order = phase1_order(n, m, trip)
                    assert (Y, sorted(set(range(m)) - {y for y in Y if y is not None})) == construct.phase1(n, m, trip)
                    X = construct.construct(n, m, trip)
                    if X is None: fails += 1
                    elif any(sum(1 for g in range(m) if X[g] == j) >= 3 for j in range(n)): large += 1
                    lines.append(f"{n} {m}|{' '.join(str(g) for tr in trip for g in tr)}|{' '.join(map(str, order))}|"
                                 + ('-' if X is None else ' '.join(map(str, X))))
    with tempfile.TemporaryDirectory() as d:
        data, runner = os.path.join(d, 'cases.txt'), os.path.join(d, 'runner.lean')
        open(data, 'w').write('\n'.join(lines) + '\n')
        open(runner, 'w').write(RUNNER)
        print(f"n = {ns}, every {every}-th profile: {len(lines)} (core, profile) pairs, "
              f"{large} with a bundle of >= 3 goods, {fails} where construct.py fails", flush=True)
        r = subprocess.run(['lake', 'env', 'lean', '--run', runner, data], cwd=os.path.join(ROOT, 'lean'),
                           capture_output=True, text=True)
        print(r.stdout.strip() or r.stderr.strip())
        sys.exit(r.returncode)

if __name__ == '__main__':
    main()
