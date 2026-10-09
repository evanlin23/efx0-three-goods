"""K3S without the rotation (rotate=False): how often is it needed, per leader rule?
  index : K3S's choice (smallest index)
  lb    : construction LB's lookahead (min |NA| after the leader's block, minus certain upgrades)
  P     : a leader satisfying the provable condition of Lemma T if one exists (its block ends with two free agents
          that stay free, or its b and c are tops of two other agents), else index
  P_lb  : P, else lb
Also counts runs in which P's condition held at some insertion step (then no rotation is needed, by Lemma T)."""
import sys, os, collections, multiprocessing, random
sys.path.insert(0, os.path.dirname(__file__))
from k3s import k3s, efx0, LEADERS, provable
from lbx import core_profiles
from test_k3s import gen_small
RULES = ['index', 'lb', 'P', 'P_lb']

def work(a):
    n, m, rank = a
    v = [dict(zip(r, (4, 3, 2))) for r in rank]; out = []
    for L in RULES:
        info = {}; X = k3s(n, m, v, info, leader=L, rotate=False)
        out.append((L, X is None, X is not None and not efx0(n, m, v, X)))
    return n, out, (rank, m)

def run(src, label):
    tot = 0; need = collections.Counter(); bad = collections.Counter(); first = {}
    with multiprocessing.Pool(4) as pool:
        for n, out, inst in pool.imap_unordered(work, src, chunksize=500):
            tot += 1
            for L, nr, nb in out:
                if nr: need[L] += 1; first.setdefault(L, inst)
                if nb: bad[L] += 1
    print(f"{label}: {tot} profiles; would need a rotation: " + ", ".join(f"{L} {need[L]}" for L in RULES)
          + (f"; NOT EFX0 {dict(bad)}" if bad else ""), flush=True)
    for L in RULES:
        if L in first: print(f"    first for {L}: {first[L]}", flush=True)

if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'cores': run(core_profiles(int(sys.argv[2])), f"cores n <= {sys.argv[2]}")
    elif what == 'cores6': run(core_profiles(6, sample=int(sys.argv[2]), minn=6), f"cores n = 6 ({sys.argv[2]} per core)")
    elif what == 'small':
        for nm in sys.argv[2:]:
            n, m = map(int, nm.split(',')); run(gen_small(n, m), f"all profiles n={n} m={m}")
    elif what == 'rprof':
        K = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
        def gen():
            for _ in range(K):
                n = rng.randint(2, 9); m = rng.randint(max(3, n), 2 * n + 3)
                yield n, m, [tuple(rng.sample(range(m), 3)) for _ in range(n)]
        run(gen(), f"random profiles n <= 9 ({K})")
