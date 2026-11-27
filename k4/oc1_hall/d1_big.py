"""Finding D1's reduction at larger n (k4/oc1_hall.md §21), by SAT (big_sstar.sstar_sat, an encoding independent of
the brute force ohlib.shaped_completion used at n <= 5).  Sampled orders of random instances; at every one-absorber-hard
start (oc_absorb.extends_A) with exactly one dangerous agent k, over the canonical chains from k with an unfrozen head
and the inclusion-minimal improving H_0 inside (J + B_{x_t}) & R_k, owner k:
  RED   chains free of HEAD and CROWD have an S* completion owned by k (Lemma D1-red: proved; a cross-check);
  CPROP chains without HEAD, with the favourites of U' distinct and in J, and an H_0 inside Pi_k - B(U') that does not
        both crowd the head and contain Y_{x_t}: that H_0 repairs (Proposition D1-C': proved; a cross-check);
  LONG  some longest chain repairs (Conjecture D1-LONG);  ANY: some chain repairs (Finding D1, canonical form).

    python3 k4/oc1_hall/d1_big.py cores:FILE N SEED ORDERS | big:N COUNT SEED ORDERS
"""
import sys, os, json, random, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set, threatened
from greedy_rules import canonical_paths, apply_chain
from big_sstar import sstar_sat, instances
from sdclib import Enc
from oc_absorb import extends_A


def minimal_improving(I, k, pk, ground):
    imp = [H for r in range(1, len(ground) + 1) for H in itertools.combinations(ground, r) if I.val(k, H) > pk]
    return [H for H in imp if not any(set(K) < set(H) for K in imp)]


if __name__ == '__main__':
    spec = sys.argv[1]; seed = int(sys.argv[3]); NORD = int(sys.argv[4]); rng = random.Random(seed)
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/d1_big.py', *sys.argv[1:], flush=True)
    def bad(tag, *a):
        C[tag] += 1
        if C['shown ' + tag] < 3: C['shown ' + tag] += 1; print(tag, *a, flush=True)
    for name, sets, vals, m in instances(spec, rng):
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); n = I.n; seen = set(); C['instances'] += 1
        for _ in range(NORD):
            od = rng.sample(range(n), n); Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); P = Picks(I, Y)
            if len(P.D) != 1: continue
            base = base_of_picks(I, Y)
            if extends_A(E, base, 1): continue
            k = P.D[0]; inst = json.dumps((sets, vals)); C['hard starts with |D| = 1'] += 1
            rep = {}
            for path in canonical_paths(I, P, k):
                xt = path[-1]
                if xt in P.F: continue
                Pi = list(P.J) + ([Y[xt]] if Y[xt] is not None else [])
                Pik = [g for g in Pi if g in I.R[k]]
                Up = [u for u in range(n) if u not in path and u not in P.F and sum(1 for g in Pik if g in I.R[u]) >= 2]
                fav = {u: max((g for g in Pi if g in I.R[u]), key=lambda g: I.key[u][g]) for u in Up}
                Bs = [fav[u] for u in Up]
                cprop = len(set(Bs)) == len(Bs) and all(b in P.J for b in Bs)
                avoid = set(minimal_improving(I, k, P.pv[k], [g for g in Pik if g not in Bs])) if cprop else set()
                for H0 in minimal_improving(I, k, P.pv[k], Pik):
                    b2 = apply_chain(I, P, base, path, H0); B2 = bundles_of(I, b2)
                    F2 = set(frozen_set(I, b2)); J2 = [g for g in range(m) if b2[g] < 0]
                    hold = [j for j in range(n) if len(B2[j]) <= 1 and j not in F2 and j != k]
                    pv2 = [I.val(i, B2[i]) for i in range(n)]
                    head = xt in F2 and threatened(I, xt, pv2[xt], list(H0) + J2)
                    crowded = [u for u in hold if len([g for g in H0 if g in I.R[u]]) >= 2 and I.val(u, [g for g in H0 if g in I.R[u]]) > pv2[u]]
                    ok = sstar_sat(E, I, b2, owner=k); rep.setdefault(path, []).append(ok)
                    C['chains'] += 1; C['chains repairing'] += ok
                    if not head and not crowded:
                        C['  RED: chains free of HEAD and CROWD'] += 1
                        if not ok: bad('RED FAILS', name, inst, 'order', od, 'picks', Y, 'chain', path, 'H0', H0)
                    if not head and cprop and H0 in avoid and not (xt in crowded and Y[xt] in H0):
                        C['  CPROP: chains covered by Proposition D1-C\''] += 1
                        if not ok: bad('CPROP FAILS', name, inst, 'order', od, 'picks', Y, 'chain', path, 'H0', H0)
                    if head: C['  chains with HEAD'] += 1; C['  chains with HEAD that repair'] += ok
            if not rep: bad('NO CANONICAL CHAIN', name, inst, Y); continue
            L = max(len(p) for p in rep)
            long_ok = any(any(v) for p, v in rep.items() if len(p) == L); any_ok = any(any(v) for v in rep.values())
            C['LONG: some longest chain repairs'] += long_ok; C['ANY: some chain repairs'] += any_ok
            if not long_ok: bad('LONG FAILS', name, inst, 'order', od, 'picks', Y, 'k', k, 'some chain repairs:', any_ok)
        if C['instances'] % 200 == 0: print('...', C['instances'], 'instances', C['hard starts with |D| = 1'], 'starts', '%.0f s' % (time.time() - t0), flush=True)
    for k_ in sorted(C):
        if not k_.startswith('shown'): print(k_, C[k_])
    print('time %.0f s' % (time.time() - t0))
