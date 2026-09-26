"""Cross-check the Lean algorithm EFX.K3.algo (lean/EFX/K3Cost.lean) against k3algo.py, and record the operation
count EFX.K3.algoC reports next to the proved bound 400 (n + m + 1)^4 (EFX.K3.algoC_cost).

For random instances (the same generators as k3algo.py --cross, plus larger random cores), this script writes a Lean
file that evaluates `algo` and `(algoC I hn).cost` on each instance (`#eval`), runs it with `lake env lean`, and
compares the allocation with `mirror` and `fast` of k3algo.py; it also checks the Lean allocation against the raw
EFX0 definition. Evidence only: it tests that the Lean program and the Python programs compute the same function
on these instances.

Usage (from the repository root or k3/):  python3 k3/lean_crosscheck.py N [--seed=S] [--max-n=K] [--rot=R] [--cores=C:n1,n2,..]
  --rot=R adds R random instances on which LB+ rotates; --cores=C:n1,n2 adds C random cores for each listed n.
"""
import sys, os, random, subprocess, tempfile, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from k3algo import mirror, fast, raw_efx0, random_core, random_instance, random_hard

LEAN_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'lean')

def lean_table(n, m, v):
    return '[' + ', '.join('[' + ', '.join(str(v[i].get(g, 0)) for g in range(m)) + ']' for i in range(n)) + ']'

HEADER = """import EFX.K3CostBound
open EFX

/-- Run algorithm K3ALG on the instance with values `tbl` (agent-major); the allocation and the operation count. -/
def runK3 (n m : Nat) (tbl : List (List Nat)) : List Nat × Nat :=
  if h : 0 < n then
    let I : Inst := ⟨n, m, fun i g => (tbl.getD i.val []).getD g.val 0⟩
    ((List.finRange m).map (fun g => (K3.algo I h g).val), (K3.algoC I h).cost)
  else ([], 0)
"""

def main():
    args = sys.argv[1:]
    opt = {a.split('=')[0]: a.split('=')[1] for a in args if a.startswith('--') and '=' in a}
    N = int([a for a in args if not a.startswith('--')][0])
    rng = random.Random(int(opt.get('--seed', 1)))
    maxn = int(opt.get('--max-n', 9))
    insts = []
    for t in range(N):
        kind = t % 3
        n = rng.randint(1, maxn)
        if kind == 0:
            m = rng.randint(max(3, n // 2), 2 * n + 2); v = random_core(n, m, rng)
        elif kind == 1:
            m = rng.randint(1, 2 * n + 3); v = random_instance(n, m, rng)
        else:
            m = rng.randint(3, 2 * n + 1); v = random_hard(n, m, rng)
        insts.append((n, m, v))
    if '--rot' in opt:                         # instances on which LB+ rotates (found by random search with fast)
        want, found = int(opt['--rot']), 0
        while found < want:
            n = rng.randint(3, maxn); m = rng.randint(3, 2 * n + 1)
            v = random_hard(n, m, rng)
            if fast(n, m, v)[1]['branch'].startswith('rot'):
                insts.append((n, m, v)); found += 1
    if '--cores' in opt:                       # larger random cores for the cost counts: C instances per listed n
        c, ns = opt['--cores'].split(':')
        for n in map(int, ns.split(',')):
            for _ in range(int(c)):
                m = rng.randint(n + 1, 2 * n)
                insts.append((n, m, random_hard(n, m, rng) if rng.random() < 0.5 else random_core(n, m, rng)))
    src = HEADER + ''.join(f'#eval IO.println (toString (runK3 {n} {m} {lean_table(n, m, v)}))\n' for n, m, v in insts)
    fd, path = tempfile.mkstemp(suffix='.lean', dir=os.environ.get('TMPDIR'))
    with os.fdopen(fd, 'w') as f: f.write(src)
    t0 = time.time()
    out = subprocess.run(['lake', 'env', 'lean', path], cwd=LEAN_DIR, capture_output=True, text=True)
    os.unlink(path)
    lines = [l for l in out.stdout.splitlines() if l.startswith('(')]
    if out.returncode != 0 or len(lines) != len(insts):
        print(out.stdout[-2000:], out.stderr[-2000:]); sys.exit(1)
    tally = collections.Counter(); worst = collections.defaultdict(float)
    for (n, m, v), line in zip(insts, lines):
        alloc_s, cost_s = line[1:-1].rsplit(', ', 1)
        X = [int(x) for x in alloc_s.strip('[]').split(', ')] if alloc_s != '[]' else []
        cost = int(cost_s)
        Xm, info = mirror(n, m, v)
        Xf, _ = fast(n, m, v)
        if X != Xm or X != Xf:
            print('MISMATCH', n, m, v, X, Xm, Xf); sys.exit(1)
        if not raw_efx0(n, m, v, X):
            print('NOT EFX0', n, m, v, X); sys.exit(1)
        bound = 400 * (n + m + 1) ** 4
        if cost > bound:
            print('COST ABOVE THE PROVED BOUND', n, m, cost, bound); sys.exit(1)
        tally[info['branch']] += 1
        worst[n] = max(worst[n], cost / (n + m + 1) ** 4)
    print(f"lean_crosscheck: {len(insts)} instances; Lean algo == mirror == fast on every one; every Lean output raw "
          f"EFX0; every operation count <= 400 (n + m + 1)^4 ({time.time() - t0:.0f} s)")
    print("branches:", dict(sorted(tally.items())))
    print("largest count / (n + m + 1)^4 by n:", {k: round(worst[k], 3) for k in sorted(worst)})

if __name__ == '__main__':
    main()
