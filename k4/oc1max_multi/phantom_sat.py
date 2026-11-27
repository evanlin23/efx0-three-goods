"""Satisfied and active phantoms (k4/oc1max_multi.md §14): at every failing start, for E(k) (every order) with k's best
improving pool pair T*, whether the settled k is satisfied (v_k(R_k - T*) <= v_k(T*)) or active, and whether its
extra good l is a pick or a pool good; for l a pick held by q, whether q is content with l alone (charity's
Proposition PH-L: v_q(R_q - l - T*) <= v_q(l) and v_q(T* - h) <= v_q(l)) and whether q is itself dangerous.

    python3 k4/oc1max_multi/phantom_sat.py FILE.jsonl[.gz] [...]   (rows with sets, vals, picks, order or orders)
"""
import sys, json, gzip, itertools, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mmlib import Inst, base_from_picks, junk, dangerous
from reduce_s import earliest_chain
for fn in sys.argv[1:]:
    C = collections.Counter()
    for l in (gzip.open(fn, 'rt') if fn.endswith('.gz') else open(fn)):
        r = json.loads(l); I = Inst(r['sets'], r['vals']); b = base_from_picks(tuple(r['picks'])); J = junk(I, b)
        p = [I.V(i, b[i]) for i in range(I.n)]; st = collections.Counter()
        for o in (r.get('orders') or [r['order']]):
            for k in dangerous(I, b):
                P = earliest_chain(I, b, k, o)
                pairs = [T for T in itertools.combinations([g for g in J + list(b[P[-1]]) if g in I.R[k]], 2) if I.V(k, T) > p[k]]
                if not pairs: continue
                Ts = max(pairs, key=lambda T: I.V(k, T)); tau = I.V(k, Ts)
                out = [g for g in I.R[k] if g not in Ts]
                sat = I.V(k, out) <= tau
                lp = [g for g in out if g != b[k][0]]
                kind = 'satisfied' if sat else ('active, l a pick' if lp and lp[0] not in J + list(b[P[-1]]) else 'active, l a pool good')
                st[kind] += 1
                if kind == 'active, l a pick':      # charity's PH-L: is l's holder q content with l alone?
                    l = lp[0]; q = [i for i in range(I.n) if b[i] and b[i][0] == l][0]
                    rest = [g for g in I.R[q] if g != l and g not in Ts]
                    content = I.V(q, rest) <= I.v[q][l] and all(I.V(q, [x for x in Ts if x != h]) <= I.v[q][l] for h in Ts)
                    st['  l-pick: q content with l alone' if content else '  l-pick: q not content'] += 1
                    st['  l-pick: q is dangerous (a sharer)' if q in dangerous(I, b) else '  l-pick: q not dangerous'] += 1
                    if content: st['  any content'] += 1
        for kk in st: C['settlements: ' + kk] += st[kk]
        C['starts where some active l-pick settlement has q content'] += bool(st['  any content'])
        C['starts with an active l-pick settlement'] += bool(st['active, l a pick'])
        C['starts'] += 1; C['starts with some satisfied best-pair settlement'] += bool(st['satisfied'])
    print(fn.split('/')[-1], dict(C))
