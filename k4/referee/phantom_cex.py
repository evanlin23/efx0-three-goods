#!/usr/bin/env python3
"""A hand-built instance (referee, k4/referee/oc1max_multi.md §13): the phantom class of k4/oc1max_multi.md §14, as
stated, admits a settle-delete-recurse step that releases into the junk a pick the phantom values above its
threshold. Own code (cert_ref, rec_s_ref helpers)."""
import itertools, json, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from cert_ref import val, efx0, sd
from rec_s_ref import earliest_wanter_chain, reduce_inst
from multi_ref import frozen_set
from oc1hall_ref import threatened

m = 8
v = [[10, 0, 0, 0, 0, 0, 6, 5],   # x = 0: top 0, junk pair {6, 7} worth 11
     [9, 5, 0, 0, 0, 0, 0, 0],    # q = 1: wants 0, picks 1
     [0, 10, 6, 0, 4, 3, 0, 0],   # k = 2: values l = 1 at 10 > v(T) = 7 > p = 6
     [0, 0, 8, 4, 0, 0, 0, 0]]    # w = 3: wants 2, picks 3
sigma = [0, 1, 2, 3]
Y = sd(v, sigma); J = set(range(m)) - set(Y)
F = frozen_set(v, [{y} for y in Y]); D = sorted(d for d in F if any(v[d][g] > 0 for g in J))
out = dict(picks=Y, J=sorted(J), frozen=sorted(F), D=D)
k = 2; E = earliest_wanter_chain(v, Y, sigma, k); T = {4, 5}; tau = val(v, k, T)
out.update(E_k=E, T=sorted(T), tau_k=tau, k_values_l1=v[k][1])
agents, goods, vm, Ym, B1 = reduce_inst(v, Y, E, T)
out["SD_E_holds"] = list(sd(vm, [agents.index(a) for a in sigma if a != k])) == list(Ym)
Bm = [{y} for y in Ym]; Jm = set(range(len(goods))) - set(Ym)
Fm = frozen_set(vm, Bm); Dm = sorted(agents[d] for d in Fm if any(vm[d][g] > 0 for g in Jm))
out.update(I_minus_agents=agents, I_minus_picks=[goods[g] for g in Ym], I_minus_junk=sorted(goods[g] for g in Jm), I_minus_D=Dm)
k2 = agents.index(0); sig = [agents.index(a) for a in sigma if a != k]
E2 = earliest_wanter_chain(vm, list(Ym), sig, k2); T2 = {6, 7}
out.update(E_k2=[agents[a] for a in E2], T2=sorted(T2), T2_improving=val(v, 0, T2) > v[0][Y[0]],
           T2_threatens_phantom_k=threatened(v, k, T2, tau))
# state after both settlements, in I
S = [set() for _ in range(4)]
S[2] = set(T); S[0] = set(T2); S[3] = {2}; S[1] = {0}       # w took Y_k = 2; q took Y_x = 0
rest = sorted(set(range(m)) - set().union(*S))
out["junk_after_two_settlements"] = rest
out["phantom_values_a_junk_good_above_threshold"] = any(v[k][g] > tau for g in rest)
# every allocation of the remaining goods to the two real agents q, w
ok = []
for f in itertools.product([1, 3], repeat=len(rest)):
    X = [set(s) for s in S]
    for g, a in zip(rest, f):
        X[a].add(g)
    if efx0(v, X):
        ok.append([sorted(x) for x in X])
out["EFX0_completions_with_k_and_x_kept"] = ok
print(json.dumps(out))
