"""Coverage of validate_random: how often bundle != base, how often a dynamically frozen agent occurs,
and how often the owner's bundle lies inside some R_j in a brute-force solution. Plus biased generator:
owners with a one-good base whose better goods are other agents' one-good bases (needed only by the owner)."""
import random, sys, itertools
from lb4r import Inst, output_sat, output_brute, output_check, all_needs, base_of

seed = int(sys.argv[1]); trials = int(sys.argv[2])
rng = random.Random(seed)
st = {"cases": 0, "mismatch": 0, "bundle_ne_base": 0, "dyn": 0, "dyn_sat": 0, "sat": 0}
for trial in range(trials):
    n = rng.randint(2, 4); m = rng.randint(4, 7)
    v = [[(rng.randint(1, 12) if rng.random() < 0.7 else 0) for g in range(m)] for i in range(n)]
    inst = Inst(v)
    base = [-1]*m; pick = [-1]*n; marked = [False]*n
    goods = list(range(m)); rng.shuffle(goods); it = iter(goods)
    for i in range(n):
        g = next(it, None)
        if g is not None and v[i][g] > 0:
            base[g] = i; pick[i] = g
        elif g is not None:
            base[g] = i; marked[i] = True
    J = [g for g in range(m) if base[g] == -1]
    if n ** len(J) > 5000: continue
    s = (tuple(base), tuple(pick), tuple(marked)); needs = all_needs(inst, s)
    for o in [None] + list(range(n)):
        res = {}
        for conv in ("bundle", "base"):
            ok, X = output_sat(inst, s, o, conv, needs, want_model=True)
            bf = output_brute(inst, s, o, conv)
            st["cases"] += 1; st["sat"] += bf
            if ok != bf or (ok and not output_check(inst, s, o, X, conv, needs)):
                st["mismatch"] += 1; print("MISMATCH", v, s, o, conv)
            res[conv] = bf
        if res["bundle"] != res["base"]:
            st["bundle_ne_base"] += 1
            assert res["bundle"] and not res["base"], "base success must imply bundle success"
        if o is not None:
            for j in range(n):
                B = base_of(inst, s, j)
                if j != o and len(B) == 1 and v[o][B[0]] > 0 and not any(B[0] in needs[i] for i in range(n) if i != o):
                    st["dyn"] += 1; st["dyn_sat"] += res["bundle"]; break
print(st)
