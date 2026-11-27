"""The RING residue of k4/oc1max_multi.md section 11 recomputed with this workstream's code, and its base classes.

RING (own definition, following multi section 5): a hard perfect start of the multi data (8,383 rows) at which no
canonical chain from a dangerous agent k (agents after k take no junk; k takes any improving H0 inside the junk plus
the end's good) is followed by an S* completion owned by k.  S* with owner o: every holder other than o (unfrozen,
at most one base good) takes at most one junk good; frozen agents and multi-good holders take nothing; raw EFX0.
For each RING start: the least base class (base.py C0..C3), whether pure reduction repairs it (form (i) of
base_census.py), and the shapes of its C0 repairs.

    python3 k4/base_phantom/ring2.py
"""
import sys, os, json, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bplib import Inst, State, start_state, bits, load_rows, row_key, dangerous, canonical_chains, submasks, frozen, \
    one_absorber
from base import base_repairs
from base_census import repairs, FORMS

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_base_phantom', 'data')


def sstar(I, S, nb, o):
    S2 = State(S.alive, S.goods, nb, S.dead)
    recv = [o] + [u for u in S.alive if u != o and nb[u] & (nb[u] - 1) == 0 and not frozen(I, S2, u)]
    return one_absorber(I, nb, recv, S2.junk(), owners=[o])


def canonical_k_repair(I, S):
    J = S.junk()
    for k in dangerous(I, S):
        for P in canonical_chains(I, S, k):
            for H0 in submasks((J | S.B[P[-1]]) & I.R[k]):
                if I.V(k, H0) <= I.V(k, S.B[k]):
                    continue
                nb = list(S.B)
                nb[k] = H0
                for a in range(1, len(P)):
                    nb[P[a]] = S.B[P[a - 1]]
                if sstar(I, S, nb, k) is not None:
                    return True
    return False


def job(r):
    I = Inst(r['sets'], r['vals'])
    S = start_state(I, r['picks'])
    if canonical_k_repair(I, S):
        return r, None
    c, w = base_repairs(I, S)
    pure = repairs(I, S, FORMS['(i)'], {})
    return r, (c, w, pure)


if __name__ == '__main__':
    rows = {}
    for r in load_rows(os.path.join(DATA, 'onemove_hard_multi.jsonl.gz')):
        rows.setdefault(row_key(r), r)
    print('$ python3 k4/base_phantom/ring2.py')
    print('distinct multi starts:', len(rows))
    C = collections.Counter()
    ex = {}
    with mp.Pool(4) as pool:
        for r, res in pool.imap_unordered(job, list(rows.values()), chunksize=16):
            if res is None:
                continue
            c, w, pure = res
            P, H0, Hs, X, f = w
            D = dangerous(Inst(r['sets'], r['vals']), start_state(Inst(r['sets'], r['vals']), r['picks']))
            shape = (c, 'len %d' % f['len'], 'ring' if f['ring'] else 'chain', 'end in D' if P[-1] in D else 'end not in D')
            C[('RING start', shape, 'pure reduction repairs' if pure else 'pure reduction FAILS')] += 1
            sz = (len(r['sets']), 1 + max(max(s) for s in r['sets']))
            if shape not in ex or sz < ex[shape][0]:
                ex[shape] = (sz, r['name'], r['picks'], list(P), bits(H0), [bits(h) for h in Hs], [bits(x) for x in X])
    print('RING starts:', sum(C.values()))
    for k in sorted(C, key=str):
        print('  %4d  %s' % (C[k], k))
    for k in sorted(ex, key=str):
        print('  smallest', k, ex[k])
