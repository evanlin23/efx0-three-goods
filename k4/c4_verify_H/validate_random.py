"""Validate output_sat (SAT encoding) against output_brute (every map junk -> agents, raw Lean definitions)
on random small states, both owner-needs conventions, every owner and no owner.
Also checks every SAT model with the literal checker."""
import random
import sys
from lb4r import Inst, output_sat, output_brute, output_check, all_needs

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
trials = int(sys.argv[2]) if len(sys.argv) > 2 else 400
rng = random.Random(seed)
stats = {"cases": 0, "sat": 0, "unsat": 0, "mismatch": 0, "dyn_cases": 0}
for trial in range(trials):
    n = rng.randint(2, 4)
    m = rng.randint(3, 8 if n <= 3 else 7)
    v = [[(rng.randint(1, 12) if rng.random() < 0.6 else 0) for g in range(m)] for i in range(n)]
    inst = Inst(v)
    # random state: some agents marked with random base; unmarked agents hold their pick or nothing
    base = [-1] * m
    pick = [-1] * n
    marked = [False] * n
    goods = list(range(m))
    rng.shuffle(goods)
    it = iter(goods)
    for i in range(n):
        if rng.random() < 0.35:
            marked[i] = True
            kk = rng.choice([0, 1, 1, 2, 2, 3])
            for _ in range(kk):
                g = next(it, None)
                if g is not None:
                    base[g] = i
        else:
            if rng.random() < 0.85:
                g = next(it, None)
                if g is not None:
                    base[g] = i
                    pick[i] = g
    # junk budget for brute force
    J = [g for g in range(m) if base[g] == -1]
    if n ** len(J) > 5000:
        continue
    s = (tuple(base), tuple(pick), tuple(marked))
    needs = all_needs(inst, s)
    for conv in ("bundle", "base"):
        for o in [None] + list(range(n)):
            ok, X = output_sat(inst, s, o, conv, needs, want_model=True)
            bf = output_brute(inst, s, o, conv)
            stats["cases"] += 1
            stats["sat" if bf else "unsat"] += 1
            if ok and not output_check(inst, s, o, X, conv, needs):
                print("MODEL FAILS CHECK", v, s, o, conv, X)
                stats["mismatch"] += 1
            if ok != bf:
                print("MISMATCH", v, s, o, conv, "sat" if ok else "unsat", "brute", bf)
                stats["mismatch"] += 1
print(stats)
