"""Conjecture OPB_n at n = 4 (kgen/n3.md §14.1): from every order whose four picks exist, is there an EFX0 allocation
with exactly one pick in each bundle whose non-trivial cycles are improving rings?  Enumerates only one-pick-per-bundle
allocations (24 pick permutations times 4^|J|).  Also records:
  - the fewest non-trivial cycles (rings) achievable;
  - whether one ring suffices with the absorber condition: at most one agent holds two or more goods outside its base,
    where ring agents' bases are their held pick plus their positively valued unpicked goods, and fixed agents' bases
    are their own pick, except that one fixed agent may take all its positively valued unpicked goods (a t = 0 move).
    This is "OC1 through OPB";
  - the same with two rings ("OC2 through OPB").
Kinds: kgen/hunt_n.py's gen_n (general, zeros, ident, klim:4, klim:5).

With SEED = 0 the two known n = 4 counterexamples to OC1 (kgen/opb_n4.py) are run first.

    python3 kgen/opb4.py SEED N MMIN MMAX"""
import sys, random, itertools, collections, json
from hunt_n import gen_n
from opb_n4 import picks, efx0, cycles


def absorber_ok(v, X, y, sig, J, cyc):
    n = len(v); ring = {i for c in cyc if len(c) > 1 for i in c}
    out = []
    for i in range(n):
        base = ({y[sig[i]]} | {g for g in X[i] & J if v[i][g] > 0}) if i in ring else {y[i]}
        out.append(len(X[i] - base))
    fixed = [i for i in range(n) if i not in ring]
    best = sum(1 for k in out if k >= 2)
    for f in fixed:                        # a t = 0 move at one fixed agent
        k2 = len(X[f] - {y[f]} - {g for g in X[f] & J if v[f][g] > 0})
        best = min(best, sum(1 for i in range(n) if (k2 if i == f else out[i]) >= 2))
    return best <= 1


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); rng = random.Random(seed); C = collections.Counter(); shown = 0
    print('$ python3 kgen/opb4.py', *sys.argv[1:], flush=True)
    kinds = ['general', 'zeros', 'ident', 'klim:4', 'klim:5']
    from opb_n4 import INST
    todo = [('known OC1 counterexample', v) for v, o in INST] if seed == 0 else []
    for t in range(N):
        kind = kinds[t % len(kinds)]; m = rng.randint(lo, hi); todo.append((kind, gen_n(kind, 4, m, rng)))
    for kind, v in todo:
        m = len(v[0]); n = 4
        seen = set()
        for o in itertools.permutations(range(n)):
            y = picks(v, o)
            if any(g is None for g in y) or tuple(y) in seen: continue
            seen.add(tuple(y)); P = set(y); J = sorted(set(range(m)) - P); pos = {g: i for i, g in enumerate(y)}
            C[kind + ': starts (distinct pick vectors)'] += 1
            minring, oc1, oc2 = None, False, False
            for perm in itertools.permutations(range(n)):          # agent i holds y[perm[i]]
                cyc = cycles(list(perm)); nontriv = [c for c in cyc if len(c) > 1]
                for q in itertools.product(range(n), repeat=len(J)):
                    X = [{y[perm[i]]} for i in range(n)]
                    for g, i in zip(J, q): X[i].add(g)
                    if not all(v[i][y[perm[i]]] + sum(v[i][g] for g in X[i] if g in J and v[i][g] > 0) > v[i][y[i]] for c in nontriv for i in c): continue
                    if not efx0(v, X): continue
                    c = len(nontriv); minring = c if minring is None else min(minring, c)
                    if absorber_ok(v, X, y, perm, set(J), cyc):
                        if c <= 1: oc1 = True
                        if c <= 2: oc2 = True
            C[kind + ': OPB with improving rings exists'] += minring is not None
            if minring is not None: C[kind + ': fewest rings = %d' % minring] += 1
            C[kind + ': OC1 through OPB (one ring, absorber condition)'] += oc1
            C[kind + ': OC2 through OPB (two rings, absorber condition)'] += oc2
            if minring is None and shown < 4:
                shown += 1; print('NO OPB', kind, json.dumps(v), 'order', o, 'picks', y, flush=True)
    for k in sorted(C): print(C[k], k)
