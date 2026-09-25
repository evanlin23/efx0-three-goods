"""Task 4: C4-exists witnesses for H_t, checked literally against PreAllocK.SoundCompletion:
  needs      : for i != o, Needs (value-based lower bound, upper bound R_i minus B_i)
  valid      : (V1), (V2) with the owner's needs replaced by N_o^X
  completion : Completion with those needs (owner listed and not frozen; frozen non-owners get no junk;
               free non-owners |C_j| + |B_j| <= 2; every base good with its agent)
  oc         : (OC4)
Witness 1: the section 7 allocation, bases = bundles for every agent, value-based needs, owner l.
Witness 2: base of l = {g1} only, the rest of l's bundle junk (a pre-allocation with junk), owner l.
Witness 3: an LB4^r state with 4 rotations (gadgets 1-4, O = {b}) and the MILP completion, owner l."""
import sys
from hcore import build_H, explicit_alloc, efx0_raw
from lb4r import Inst, phase1_state, rot_steps, all_needs, output_sat


def sound_completion(v, base, N, o, X):
    n, m = len(v), len(v[0])
    B = [[g for g in range(m) if base[g] == i] for i in range(n)]
    bund = [[g for g in range(m) if X[g] == i] for i in range(n)]
    errs = []
    for i in range(n):
        if i == o:
            continue
        vb = sum(v[i][g] for g in B[i])
        for g in range(m):
            if base[g] != i and vb < v[i][g] and g not in N[i]:
                errs.append(f"Needs.lower {i} {g}")
        for g in N[i]:
            if not (v[i][g] > 0 and base[g] != i):
                errs.append(f"Needs.upper {i} {g}")
    N2 = [set(x) for x in N]
    if o is not None:
        vo = sum(v[o][g] for g in bund[o])
        N2[o] = {g for g in range(m) if X[g] != o and vo < v[o][g]}
    NA = set().union(*N2)
    J = [g for g in range(m) if base[g] == -1]
    if any(g in NA for g in J):
        errs.append("V1")
    for i in range(n):
        if len(B[i]) >= 2 and any(g in NA for g in B[i]):
            errs.append(f"V2 {i}")
    fr = [len(B[i]) == 1 and B[i][0] in NA for i in range(n)]
    if any(base[g] >= 0 and X[g] != base[g] for g in range(m)):
        errs.append("onBase")
    if o is not None and fr[o]:
        errs.append("owner frozen")
    for j in range(n):
        if j == o:
            continue
        cj = [g for g in bund[j] if base[g] == -1]
        if fr[j] and cj:
            errs.append(f"frozen {j} gets junk")
        if not fr[j] and len(cj) + len(B[j]) > 2:
            errs.append(f"free {j} too many")
    if o is not None:
        for j in range(n):
            if j == o:
                continue
            vj = sum(v[j][g] for g in bund[j])
            for h in bund[o]:
                if sum(v[j][g] for g in bund[o] if g != h) > vj:
                    errs.append(f"OC {j} {h}")
    return errs


def value_needs(v, base):
    n, m = len(v), len(v[0])
    out = []
    for i in range(n):
        vb = sum(v[i][g] for g in range(m) if base[g] == i)
        out.append({g for g in range(m) if base[g] != i and vb < v[i][g]})
    return out


T = int(sys.argv[1]) if len(sys.argv) > 1 else 8
for t in range(1, T + 1):
    agents, goods, v = build_H(t)
    n, m = len(v), len(v[0])
    X = explicit_alloc(t, agents, goods)
    bad, bund = efx0_raw(v, X, n)
    base1 = list(X)
    e1 = sound_completion(v, base1, value_needs(v, base1), 0, X)
    base2 = [(-1 if (X[g] == 0 and goods[g] != "g1") else X[g]) for g in range(m)]
    e2 = sound_completion(v, base2, value_needs(v, base2), 0, X)
    print(f"H_{t}: explicit allocation EFX0 violations={len(bad)}; witness 1 (bases = bundles) errors={e1}; "
          f"witness 2 (l's base {{g1}}, {sum(1 for g in base2 if g == -1)} junk goods) errors={e2}")
# witness 3 on H_5
t = 5
agents, goods, v = build_H(t)
inst = Inst(v)
A = {a: i for i, a in enumerate(agents)}
G = {g: i for i, g in enumerate(goods)}
s, _ = phase1_state(inst, [])
for j in (1, 2, 3, 4):
    succ = rot_steps(inst, s)
    s = [s2 for s2, (c, O) in succ.items() if c == (A[f"x{j}1"], A[f"y{j}"]) and O == (G[f"b{j}1"],)][0]
needs = all_needs(inst, s)
ok, X = output_sat(inst, s, 0, "base", needs, want_model=True, backend="milp")
e3 = sound_completion(v, list(s[0]), [set(x) for x in needs], 0, X)
bad, bund = efx0_raw(v, X, len(v))
print(f"H_5 witness 3 (4 rotations, owner l, needs from base): found={ok} SoundCompletion errors={e3} "
      f"EFX0 violations={len(bad)} bundle sizes>2: {[len(b) for b in bund if len(b) > 2]}")
