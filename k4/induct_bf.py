"""Independent brute force for k4/induct.md (shares no code with k4/induct.c).

Every allocation is enumerated with itertools.product (no pruning); EFX0 is the raw definition
v_i(X_i) >= v_i(X_j) - v_i(g) for all i != j and g in X_j. Used to re-check the claims of k4/induct.md on single
instances (the insertion tests) and to print the structure of an insertion.

Library use:
  efx0(V, own, goods, agents)          raw EFX0 test of an owner map
  all_efx0(V, goods, agents)           every EFX0 owner map (dict good -> agent)
  enviers(V, own, w, agents)           agents that envy w's bundle (v_j(X_w) > v_j(X_j))
  placements(V, own, d, agents)        agents a such that own + {d -> a} is EFX0
CLI:
  python3 k4/induct_bf.py 'SETS' 'PROF' w d     (SETS, PROF as JSON; PROF[i] are values on SETS[i] in order)
      prints every EFX0 allocation X' of I - d with its enviers of w, the potentials of k4/induct.md, and the
      placements of d that keep EFX0; then the insertion claim for the minimizers of #enviers(w).
"""
import itertools, json, sys


def valuation(sets, prof, m):
    V = [[0] * m for _ in sets]
    for i, (S, t) in enumerate(zip(sets, prof)):
        for g, x in zip(S, t): V[i][g] = x
    return V


def bundles(own, agents):
    B = {a: [] for a in agents}
    for g, a in own.items(): B[a].append(g)
    return B


def efx0(V, own, agents):
    B = bundles(own, agents)
    for i in agents:
        mine = sum(V[i][g] for g in B[i])
        for j in agents:
            if j == i: continue
            tot = sum(V[i][g] for g in B[j])
            for g in B[j]:
                if mine < tot - V[i][g]: return False
    return True


def all_efx0(V, goods, agents):
    out = []
    for ow in itertools.product(agents, repeat=len(goods)):
        own = dict(zip(goods, ow))
        if efx0(V, own, agents): out.append(own)
    return out


def enviers(V, own, w, agents):
    B = bundles(own, agents)
    return [j for j in agents if j != w and sum(V[j][g] for g in B[w]) > sum(V[j][g] for g in B[j])]


def placements(V, own, d, agents):
    res = []
    for a in agents:
        o = dict(own); o[d] = a
        if efx0(V, o, agents): res.append(a)
    return res


def main():
    sets = json.loads(sys.argv[1]); prof = json.loads(sys.argv[2]); w = int(sys.argv[3]); d = int(sys.argv[4])
    m = 1 + max(g for S in sets for g in S)
    V = valuation(sets, prof, m)
    agents = list(range(len(sets)))
    goods = [g for g in range(m) if g != d]
    E = all_efx0(V, goods, agents)
    print(f'I - d: {len(E)} EFX0 allocations')
    best = min(len(enviers(V, X, w, agents)) for X in E)
    for X in E:
        B = bundles(X, agents)
        env = enviers(V, X, w, agents)
        pl = placements(V, X, d, agents)
        vw = sum(V[w][g] for g in B[w])
        print(f'  {[B[a] for a in agents]} enviers(w)={env} v_w={vw} placements of d: {pl}' + ('  <- min enviers' if len(env) == best else ''))
    bad = [X for X in E if len(enviers(V, X, w, agents)) == best and not placements(V, X, d, agents)]
    print(f'min #enviers(w) = {best}; minimizers with no placement of d: {len(bad)}')


if __name__ == '__main__':
    main()
