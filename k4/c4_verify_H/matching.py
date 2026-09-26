"""The matching construction: rotate x_{j,1} to y_j (O = {b_{j,1}}, or {b_{j,1}, c_{j,1}}) in r gadgets.
Every step is taken from rot_steps (so it is a legal RotStep of LB4R.lean); the final state is tested with both
encodings (A: lb4r.output_sat MILP backend, with the model checked literally; B: enc_b.output_b).
Usage: python3 matching.py t r"""
import sys
import itertools
from hcore import build_H
from lb4r import Inst, phase1_state, up_run, rot_steps, all_needs, output_sat, output_check
from enc_b import output_b

t = int(sys.argv[1])
r = int(sys.argv[2])
agents, goods, v = build_H(t)
inst = Inst(v)
A = {a: i for i, a in enumerate(agents)}
G = {g: i for i, g in enumerate(goods)}
s0, _ = phase1_state(inst, [])
for pol in ("shrink", "envyFree", "none"):
    assert up_run(inst, s0, pol)[0] == s0
found = []
for gadgets in itertools.combinations(range(1, t + 1), r):
    for Okind in ("b", "bc"):
        s = s0
        ok = True
        for j in gadgets:
            c = (A[f"x{j}1"], A[f"y{j}"])
            O = (G[f"b{j}1"],) if Okind == "b" else tuple(sorted((G[f"b{j}1"], G[f"c{j}1"])))
            succ = rot_steps(inst, s)
            nxt = [s2 for s2, (cc, OO) in succ.items() if cc == c and tuple(sorted(OO)) == O]
            if len(nxt) != 1:
                ok = False
                break
            s = nxt[0]
        if not ok:
            print(f"gadgets {gadgets} O={Okind}: not a legal rotation sequence")
            continue
        needs = all_needs(inst, s)
        res = {}
        for conv in ("bundle", "base"):
            ownersA, ownersB = [], []
            for o in [None] + list(range(inst.n)):
                okA, X = output_sat(inst, s, o, conv, needs, want_model=True, backend="milp")
                if okA:
                    assert output_check(inst, s, o, X, conv, needs)
                    ownersA.append(agents[o] if o is not None else None)
                if output_b(v, s, o, conv):
                    ownersB.append(agents[o] if o is not None else None)
            assert ownersA == ownersB, (ownersA, ownersB)
            res[conv] = ownersA
        print(f"gadgets {gadgets} O={Okind}: owners with an output: bundle={res['bundle']} base={res['base']}")
        if res["bundle"]:
            found.append((gadgets, Okind))
print(f"t={t}, {r} rotations: {len(found)} matching-construction states with an output")
