"""Cross-check the C brute force against the Python full brute force (every map junk -> agents) on random
small states; and the SAT test against both."""
import random, sys
from lb4r import Inst, output_sat, output_brute, all_needs
from bfpy import bf_output
rng = random.Random(int(sys.argv[1])); trials = int(sys.argv[2])
st = {"cases": 0, "mismatch": 0, "sat": 0}
for trial in range(trials):
    n = rng.randint(2, 4); m = rng.randint(3, 7)
    v = [[(rng.randint(1, 12) if rng.random() < 0.65 else 0) for g in range(m)] for i in range(n)]
    inst = Inst(v)
    base = [-1]*m; pick = [-1]*n; marked = [False]*n
    goods = list(range(m)); rng.shuffle(goods); it = iter(goods)
    for i in range(n):
        if rng.random() < 0.3:
            marked[i] = True
            for _ in range(rng.choice([0, 1, 2, 3])):
                g = next(it, None)
                if g is not None: base[g] = i
        elif rng.random() < 0.85:
            g = next(it, None)
            if g is not None: base[g] = i; pick[i] = g
    J = [g for g in range(m) if base[g] == -1]
    if n ** len(J) > 3000: continue
    s = (tuple(base), tuple(pick), tuple(marked)); needs = all_needs(inst, s)
    for conv in ("bundle", "base"):
        for o in [None] + list(range(n)):
            a = output_brute(inst, s, o, conv); b, _ = bf_output(inst, s, o, conv); c, _ = output_sat(inst, s, o, conv, needs)
            st["cases"] += 1; st["sat"] += a
            if not (a == b == c):
                st["mismatch"] += 1; print("MISMATCH", v, s, o, conv, a, b, c)
print(st)
