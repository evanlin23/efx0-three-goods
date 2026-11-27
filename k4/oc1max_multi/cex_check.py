"""The known OC1^max counterexamples against this workstream's lemmas (k4/oc1max_multi.md §8).

Instances: the certifier's 11 n = 4 cores (results/k4_oc1max_multi/oc1max_cex_n4_from_cert.json, copied from
compute/k4-oc1max-cert results/k4_oc1max/oc1max_cex_n4.json) and the TTC session's n = 5 strict core (k4/oc1_hall.md
§22).  For each, with this workstream's own code (mmlib, raw EFX0, enumeration):
  * re-verify: the picks form a perfect start, no one-absorber completion at the picks, and none after any official
    move (an independent check of the counterexample);
  * the structure: D, D_T (truly dangerous), unfrozen pick holders, junk-exposed unfrozen agents E_J, shared pool
    danger sets;
  * consistency: no chain satisfies the hypotheses of Lemma KEEP, Lemma OWN, Lemma D-red (clean chain) or Lemma
    RING-red, and the hypothesis of Theorem U fails (otherwise that lemma would be refuted);
  * the obstacles of every canonical chain from D with a minimal improving H_0.

    python3 k4/oc1max_multi/cex_check.py
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, frozen, dangerous, oa_absorbers, moves, is_perfect, nu
from dred import canonical_chains, improving_sets, obstacles, apply_chain
from lemma_b import truly_dangerous, keep_star_chains, keep_star_completion
from lemma_own import own_chains
from ring import rings, ring_red

TTC = {'name': 'TTC-n5-core', 'sets': [[0, 4, 5, 6], [2, 3, 4, 6], [0, 1, 5, 6], [2, 4, 5, 6], [0, 1, 7, 8]],
       'vals': [[3, 2, 10, 6], [4, 1, 6, 8], [2, 8, 5, 4], [5, 4, 8, 2], [7, 8, 2, 4]], 'order': (1, 3, 4, 2, 0)}


def instances():
    d = json.load(open(os.path.join(ROOT, 'results', 'k4_oc1max_multi', 'oc1max_cex_n4_from_cert.json')))
    for x in d['instances']:
        yield {'name': '%s#%d' % (x['list'], x['idx']), 'sets': x['sets'], 'vals': x['vals'],
               'order': tuple(x['brute_force']['example order']), 'picks': tuple(x['picks'])}
    yield TTC


def shared_pool_sets(I, base, D, J, F):
    """(k, k', T, z): k != k' in D, z unfrozen pick holder, T a minimal improving set of k inside (J + B_z) & R_k
    with v_k'(T) > p_k'  (the integrator's definition, k4/oc1_hall.md §23)"""
    p = [I.V(i, base[i]) for i in range(I.n)]; out = []
    for z in range(I.n):
        if z in F or not base[z]: continue
        for k in D:
            for T in improving_sets(I, base, k, J + list(base[z]), True):
                for k2 in D:
                    if k2 != k and I.V(k2, T) > p[k2]: out.append((k, k2, T, z))
    return out


if __name__ == '__main__':
    print('$ python3 k4/oc1max_multi/cex_check.py')
    T = collections.Counter()
    for x in instances():
        I = Inst(x['sets'], x['vals']); Y = I.sd(x['order'])
        if 'picks' in x: assert Y == x['picks'], (x['name'], Y)
        base = base_from_picks(Y); J = junk(I, base); F = set(frozen(I, base)); D = dangerous(I, base)
        DT = truly_dangerous(I, base, D, J); U = [i for i in range(I.n) if i not in F and base[i]]
        EJ = [u for u in U if I.threat(u, I.V(u, base[u]), J)]
        perfect = is_perfect(I, Y) and sum(y is not None for y in Y) == nu(I)
        hard0 = not oa_absorbers(I, base)
        one_move = [nb for nb in moves(I, base) if oa_absorbers(I, nb)]
        sh = shared_pool_sets(I, base, D, J, F)
        keep = list(itertools.islice((c for k in DT for c in keep_star_chains(I, base, k, DT, J)), 1))
        own = list(itertools.islice(own_chains(I, base, D, DT, J), 1))
        clean = []; obs = collections.Counter()
        for k in D:
            for path in canonical_chains(I, base, k):
                for H0 in improving_sets(I, base, k, J + list(base[path[-1]]), True):
                    nb, ob = obstacles(I, base, path, H0); key = '+'.join(sorted(ob - {'UNFRZ'})) or 'clean'
                    obs[key] += 1
                    if key == 'clean': clean.append((path, H0))
        ringok = []
        p = [I.V(i, base[i]) for i in range(I.n)]
        for k in D:
            for path, Ht in rings(I, base, k, J):
                d = path[-1]
                if d not in D or base[d][0] not in I.R[k]: continue
                Jk = [g for g in J if g in I.R[k] and g not in Ht]
                for r in range(len(Jk) + 1):
                    for G in itertools.combinations(Jk, r):
                        H0 = (base[d][0],) + G
                        if I.V(k, H0) > p[k] and ring_red(I, base, path, Ht, H0)[1]: ringok.append((path, Ht, H0))
        # Theorem U's hypothesis
        thmU = False
        if len(DT) == 1:
            k = DT[0]; ch = canonical_chains(I, base, k); L = max(len(c) for c in ch)
            for path in ch:
                if len(path) == L and all(u == path[-1] for u in EJ):
                    for H0 in improving_sets(I, base, k, J, False):
                        nb = apply_chain(I, base, path, H0)
                        if not (path[-1] in frozen(I, nb) and path[-1] in EJ): thmU = True
        ok = perfect and hard0 and not one_move
        bad = keep or own or clean or ringok or thmU
        T['instances'] += 1; T['verified: perfect, hard, no one-move repair'] += ok
        T['a lemma applies (would refute it)'] += bool(bad); T['shared pool danger set'] += bool(sh)
        print(x['name'], 'n=%d m=%d' % (I.n, I.m), 'picks', Y, 'J', J, 'D', D, 'D_T', DT, 'unfrozen', U, 'E_J', EJ,
              '| verified' if ok else '| NOT VERIFIED', '| shared', sh[:2], '| obstacles', dict(obs),
              '| KEEP/OWN/clean/RING/U:', bool(keep), bool(own), bool(clean), bool(ringok), thmU)
    for k in sorted(T): print(k, T[k])
