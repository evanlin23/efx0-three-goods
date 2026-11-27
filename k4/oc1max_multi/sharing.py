"""Leaf 4f of the integrator's case tree (k4/oc1_hall.md §23.2): split the hard perfect starts with |D| >= 2 by whether
they have a *shared pool danger set* (k != k' in D, an unfrozen pick holder z, a minimal improving set T of k inside
(J + B_z) & R_k with v_k'(T) > p_k').  For each class: (i) a canonical chain from some k in D repairs with an S*
completion owned by k; (ii) the first written lemma that applies (regimes.mechanism: KEEP, OWN, CLEAN = D-red,
RING = RING-red; CAN-k and ED are not lemmas); (iii) for the no-sharing class, the obstacles (HEAD, CROWD, DEMAND) of
every canonical chain with a minimal H_0 at the starts that fail (i).

    python3 k4/oc1max_multi/sharing.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen
from dred import canonical_chains, improving_sets, obstacles
from analyze import classify
from regimes import mechanism
from cex_check import shared_pool_sets

if __name__ == '__main__':
    T = collections.Counter(); ex = {}
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base); F = set(frozen(I, base)); D = rec['D']
            cls = 'shared' if shared_pool_sets(I, base, D, J, F) else 'no sharing'
            tags = classify(rec); mech, _ = mechanism(I, rec)
            T[(cls, 'starts')] += 1
            T[(cls, '(i) canonical chain, owner k')] += 'CAN-k' in tags
            T[(cls, '(ii) first mechanism ' + mech)] += 1
            T[(cls, '(ii) a written lemma applies')] += mech in ('KEEP', 'OWN', 'CLEAN', 'RING')
            if 'CAN-k' not in tags:
                obs = set()
                for k in D:
                    for path in canonical_chains(I, base, k):
                        for H0 in improving_sets(I, base, k, J + list(base[path[-1]]), True):
                            obs.add('+'.join(sorted(obstacles(I, base, path, H0)[1] - {'UNFRZ'})) or 'clean')
                T[(cls, '(iii) fails (i); obstacles seen: ' + ', '.join(sorted(obs)))] += 1
                key = (cls, 'fails (i)')
                if key not in ex or (I.n, I.m) < ex[key][0]: ex[key] = ((I.n, I.m), rec)
    print('$ python3 k4/oc1max_multi/sharing.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
    for k, ((n, m), r) in sorted(ex.items()):
        print('smallest', k, r['name'], 'n = %d, m = %d' % (n, m), json.dumps([r['inst']['sets'], r['inst']['vals']]), 'picks', r['picks'])
