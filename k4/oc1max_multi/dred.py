"""Lemma D-red census (k4/oc1max_multi.md §2): canonical chains from every dangerous agent k at the hard perfect starts
with |D| >= 2, every improving H_0, owner k.  For each chain the obstacles at the state B' are:
  HEAD   : the head x_t is frozen at B' and threatened by the pool Pi = J + B_{x_t} at its new value;
  CROWD  : some holder u != k at B' has a danger set inside H_0 (|H_0 & R_u| >= 2, v_u(H_0 & R_u) > v_u(B'_u));
  DEMAND : some d in D - {k}, frozen at B', is threatened by Pi at v_d(B'_d);
  UNFRZ  : some d in D - {k} is unfrozen at B' (a dangerous agent freed by the chain).
Lemma D-red says: with none of HEAD, CROWD, DEMAND, B' has an S* completion owned by k (H = empty).  The census checks
that, and counts how often each obstacle occurs, and whether the chain repairs (S* owned by k, raw enumeration).

    python3 k4/oc1max_multi/dred.py FILE.jsonl [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, wanters, sstar, holders


def canonical_chains(I, base, k):
    """paths k = x_0, ..., x_t (t >= 1), each x_i wanting B_{x_{i-1}} alone, head unfrozen at the base"""
    n = I.n; val = [I.V(i, base[i]) for i in range(n)]; F = set(frozen(I, base)); out = []
    def ext(path):
        xt = path[-1]
        if len(path) >= 2 and xt not in F: out.append(tuple(path))
        if xt not in F or len(path) > n: return
        g = base[xt][0]
        for y in range(n):
            if y not in path and I.v[y].get(g, 0) > val[y]: ext(path + [y])
    ext([k])
    return out


def apply_chain(I, base, path, H0):
    nb = [list(b) for b in base]; nb[path[0]] = sorted(H0)
    for i in range(1, len(path)): nb[path[i]] = list(base[path[i - 1]])
    return tuple(tuple(b) for b in nb)


def improving_sets(I, base, k, pool, minimal_only):
    p = I.V(k, base[k]); pool = [g for g in pool if g in I.R[k]]
    for r in range(1, len(pool) + 1):
        for H in itertools.combinations(pool, r):
            if I.V(k, H) <= p: continue
            if minimal_only and any(I.V(k, [g for g in H if g != h]) > p for h in H): continue
            yield H


def obstacles(I, base, path, H0):
    k, xt = path[0], path[-1]; J = junk(I, base); Pi = J + list(base[xt])
    nb = apply_chain(I, base, path, H0); val = [I.V(i, nb[i]) for i in range(I.n)]
    F2 = set(frozen(I, nb)); D = [d for d in frozen(I, base) if any(g in J for g in I.R[d])]
    ob = set()
    if xt in F2 and I.threat(xt, val[xt], Pi): ob.add('HEAD')
    for u in holders(I, nb, k):
        Hu = [g for g in H0 if g in I.R[u]]
        if len(Hu) >= 2 and I.V(u, Hu) > val[u]: ob.add('CROWD')
    for d in D:
        if d == k: continue
        if d in F2 and I.threat(d, val[d], Pi): ob.add('DEMAND')
        if d not in F2: ob.add('UNFRZ')
    return nb, ob


if __name__ == '__main__':
    T = collections.Counter(); starts = collections.Counter(); bad = []
    MIN = os.environ.get('MIN', '1') == '1'
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base)
            st = set()
            for k in rec['D']:
                for path in canonical_chains(I, base, k):
                    st.add('has canonical chain')
                    for H0 in improving_sets(I, base, k, J + list(base[path[-1]]), MIN):
                        nb, ob = obstacles(I, base, path, H0)
                        ok = sstar(I, nb, k)
                        T['chains'] += 1; T['chains repaired (S* owner k)'] += ok
                        key = '+'.join(sorted(ob - {'UNFRZ'})) or 'clean'
                        T['  ' + key] += 1; T['  ' + key + ', repaired'] += ok
                        if 'UNFRZ' in ob: T['  (UNFRZ)'] += 1; T['  (UNFRZ), repaired'] += ok
                        if key == 'clean':
                            st.add('clean chain')
                            if not ok: bad.append((rec['name'], path, H0))
                        if ok: st.add('repaired by a canonical chain, owner k')
                        if ok and key != 'clean': st.add('repaired only with an obstacle')
            starts['starts'] += 1
            for s in st: starts[s] += 1
            if 'clean chain' not in st and 'repaired by a canonical chain, owner k' in st: starts['repaired, but no clean chain'] += 1
    print('$ python3 k4/oc1max_multi/dred.py', *sys.argv[1:], '(MIN=%d)' % MIN)
    for k in sorted(T): print(k, T[k])
    for k in sorted(starts): print(k, starts[k])
    print('clean chains that do not repair (Lemma D-red violations):', len(bad), bad[:5])
