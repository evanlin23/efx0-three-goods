"""The regimes of k4/oc1max_multi.md §5: every hard perfect start with |D| >= 2, split by |D_T| (truly dangerous agents)
and by the first mechanism, in this order, that repairs it:
  KEEP    : Lemma KEEP applies (canonical chain from k in D_T, H_0 inside J, no crowding, the frozen agents of
            D_T - {k} and the head unthreatened by J, a holder admissible for the head's old pick), so the start is
            repaired by a written proof;
  OWN     : Lemma OWN applies (canonical chain in which k takes a junk pair; a free-base owner o outside {k, x_1};
            the other truly dangerous agents unthreatened by o's base plus J - H_0; a holder admissible for Y_z);
  CLEAN   : Lemma D-red applies (canonical chain, no HEAD, CROWD or DEMAND), repaired by a written proof;
  CAN-k   : some canonical chain from some k in D with an S* completion owned by k (an open sub-lemma covers it);
  ED      : some ED chain (Hall: head may add junk) with an S* completion owned by x_0 or x_t;
  ANY     : some move with a one-absorber completion;
  NONE    : no repair (a counterexample to OC1 at this perfect start).
For each (regime, mechanism) cell: the number of starts and the smallest instance.

    python3 k4/oc1max_multi/regimes.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, sstar
from dred import canonical_chains, improving_sets, obstacles
from lemma_b import truly_dangerous, keep_star_chains, keep_star_completion


def mechanism(I, rec):
    Y = tuple(rec['picks']); base = base_from_picks(Y); J = junk(I, base); D = rec['D']
    DT = truly_dangerous(I, base, D, J)
    for k in DT:
        for path, H0, nb, u in keep_star_chains(I, base, k, DT, J):
            if keep_star_completion(I, nb, k, u, base[path[-1]][0]) is None: return 'KEEP VIOLATION', DT
            return 'KEEP', DT
    from lemma_own import own_chains, own_completion
    for path, H0, nb, o, u, yz in own_chains(I, base, D, DT, J):
        if own_completion(I, nb, o, u, yz) is None: return 'OWN VIOLATION', DT
        return 'OWN', DT
    can = False
    for k in D:
        for path in canonical_chains(I, base, k):
            for H0 in improving_sets(I, base, k, J + list(base[path[-1]]), False):
                nb, ob = obstacles(I, base, path, H0); ok = sstar(I, nb, k)
                if not ({'HEAD', 'CROWD', 'DEMAND'} & ob):
                    return ('CLEAN' if ok else 'D-RED VIOLATION'), DT
                can = can or ok
    if can: return 'CAN-k', DT
    reps = rec['repairs']
    if any(r['ed'] and (set(r['ss']) & ({r['path'][0], r['path'][-1]} if r['kind'] == 'chain' else {r['path'][0]}))
           for r in reps if r['kind'] in ('chain', 'add')): return 'ED', DT
    if reps: return 'ANY', DT
    return 'NONE', DT


if __name__ == '__main__':
    T = collections.Counter(); ex = {}
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            mech, DT = mechanism(I, rec)
            reg = '|D_T| = 0' if not DT else ('|D_T| = 1' if len(DT) == 1 else '|D_T| >= 2')
            T[(reg, mech)] += 1; T[reg] += 1; T['starts'] += 1; T[mech] += 1
            size = (I.n, I.m)
            if (reg, mech) not in ex or size < ex[(reg, mech)][0]: ex[(reg, mech)] = (size, rec)
    print('$ python3 k4/oc1max_multi/regimes.py', *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    for k in sorted(ex, key=str):
        (n, m), r = ex[k]
        print('smallest', k, ':', r['name'], 'n = %d, m = %d' % (n, m), 'sets', json.dumps(r['inst']['sets']),
              'vals', json.dumps(r['inst']['vals']), 'order', r['order'], 'picks', r['picks'])
