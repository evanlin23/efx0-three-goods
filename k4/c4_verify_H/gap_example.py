"""Find a completion satisfying Output (both conventions) in which a non-owner x_{j,i} holding its pick {a_{j,i}}
has g_j in its slot while b_{j,i} and c_{j,i} are both in X_o (so neither private good is 'forced' out of X_o);
likewise l holding {g1, z} with u, u' in X_o. Uses encoding A plus unit clauses, the model checked literally."""
import itertools
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from hcore import build_H
from lb4r import Inst, phase1_state, reach, all_needs, build_model, output_check, _decode, base_of
for t in (2, 3):
    agents, goods, v = build_H(t); inst = Inst(v); A = {a: i for i, a in enumerate(agents)}; G = {g: i for i, g in enumerate(goods)}
    s0, _ = phase1_state(inst, []); levels = reach(inst, s0, 3)
    found = {"x": None, "l": None}
    for d, lev in enumerate(levels):
        for s in lev:
            needs = all_needs(inst, s)
            for o in range(inst.n):
                for conv in ("bundle",):
                    M = build_model(inst, s, o, conv, needs)
                    if M is None: continue
                    nv, clauses, cards, x, holders, J = M
                    cl = list(clauses); top = nv
                    for lits, op, b in cards:
                        if op == "==":
                            cl.append(list(lits)); cl += [[-a, -c] for a, c in itertools.combinations(lits, 2)]
                        else:
                            enc = CardEnc.atmost(lits=lits, bound=b, top_id=top, encoding=EncType.seqcounter); top = max(top, enc.nv); cl += enc.clauses
                    targets = []
                    for j in range(1, t + 1):
                        for i in (1, 2, 3):
                            xa = A[f"x{j}{i}"]; gj, b, c = G[f"g{j}"], G[f"b{j}{i}"], G[f"c{j}{i}"]
                            if xa != o and base_of(inst, s, xa) == [G[f"a{j}{i}"]] and (gj, xa) in x and (b, o) in x and (c, o) in x:
                                targets.append(("x", agents[xa], [x[(gj, xa)], x[(b, o)], x[(c, o)]]))
                    l = 0; z, u, u2 = G["z"], G["u"], G["u'"]
                    if o != l and (z, l) in x and (u, o) in x and (u2, o) in x:
                        targets.append(("l", "l", [x[(z, l)], x[(u, o)], x[(u2, o)]]))
                    for kind, who, units in targets:
                        if found[kind]: continue
                        with Solver(name="g3", bootstrap_with=cl + [[u_] for u_ in units]) as S:
                            if S.solve():
                                X = _decode(s, set(l_ for l_ in S.get_model() if l_ > 0), x, holders, J)
                                assert output_check(inst, s, o, X, conv, needs)
                                bund = {agents[i]: [goods[g] for g in range(inst.m) if X[g] == i] for i in range(inst.n)}
                                found[kind] = (d, agents[o], who, bund)
            if all(found.values()): break
        if all(found.values()): break
    for k, f in found.items():
        print(f"H_{t} [{k}]:", "none found" if f is None else f"depth {f[0]}, owner {f[1]}, protected agent {f[2]}: bundles {f[3]}")
