"""Lemma RING-red census (k4/oc1max_multi.md §6): rings through two dangerous agents, owner k.

A *dangerous ring* from k in D: agents k = x_0, x_1, ..., x_t = d (t >= 1, distinct), each x_i (1 <= i < t) wanting
Y_{x_{i-1}} at the picks; the head d takes Y_{x_{t-1}} plus junk H_t, with v_d(Y_{x_{t-1}} + H_t) > p_d; k takes
H_0 = {Y_d} + G with G inside the junk and v_k(H_0) > p_k.  No pick is released.  With owner k, Lemma 2* applies with
H = {} when
  (R1) the head's bundle threatens nobody at the state's values;
  (R2) no agent other than k wants a good of H_0;
  (R3) every agent frozen at the state (k excepted), and the head, is unthreatened by H_0 + J' (J' the new junk);
  (R4) no holder is crowded by H_0.
The census lists, at every start, the rings meeting (R1)-(R4) and checks each has an S* completion owned by k (raw
EFX0; a violation would contradict Lemma 2*), and counts the starts of each regime with such a ring.

    python3 k4/oc1max_multi/ring.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, holders, sstar


def rings(I, base, k, J):
    n = I.n; val = [I.V(i, base[i]) for i in range(n)]
    def ext(path):
        last = path[-1]
        g = base[last][0]
        for y in range(n):
            if y in path or not base[y]: continue
            # y as the head d: takes g plus junk H_t, gives Y_y to k
            if y != k:
                Jy = [h for h in J if h in I.R[y]]
                for r in range(len(Jy) + 1):
                    for Ht in itertools.combinations(Jy, r):
                        if I.V(y, [g] + list(Ht)) > val[y]: yield path + [y], Ht
            # y as a middle agent: wants g
            if I.v[y].get(g, 0) > val[y] and len(path) < n: yield from ext(path + [y])
    yield from ext([k])


def apply_ring(I, base, path, Ht, H0):
    nb = [list(b) for b in base]; nb[path[0]] = sorted(H0)
    for i in range(1, len(path)): nb[path[i]] = list(base[path[i - 1]])
    nb[path[-1]] = nb[path[-1]] + list(Ht)
    return tuple(tuple(b) for b in nb)


def ring_red(I, base, path, Ht, H0):
    k, d = path[0], path[-1]; nb = apply_ring(I, base, path, Ht, H0); n = I.n
    val = [I.V(i, nb[i]) for i in range(n)]; Jp = junk(I, nb); W = list(H0) + Jp
    if any(i != d and I.threat(i, val[i], nb[d]) for i in range(n)): return nb, False              # (R1)
    if any(i != k and I.v[i].get(g, 0) > val[i] for i in range(n) for g in H0): return nb, False     # (R2)
    F2 = set(frozen(I, nb))
    if any(I.threat(q, val[q], W) for q in list(F2) + [d] if q != k): return nb, False              # (R3)
    for u in holders(I, nb, k):                                                                       # (R4)
        Hu = [g for g in H0 if g in I.R[u]]
        if len(Hu) >= 2 and I.V(u, Hu) > val[u]: return nb, False
    return nb, True


def ring_own(I, base, path, Ht, H0, o):
    """Lemma RING-OWN: the ring with owner o != k.  Lemma 2* with H = {} applies when
      (O1) every multi-good bundle other than o's threatens nobody at the state's values;
      (O2) o holds at most one good and is unfrozen at the state;
      (O3) every non-holder other than o (frozen singletons, multi-good holders) is unthreatened by B'_o + J'.
    (O2) also excludes non-movable holders (nobody wants B'_o, and |B'_o| <= 1)."""
    k = path[0]; nb = apply_ring(I, base, path, Ht, H0); n = I.n
    if o == k: return nb, False
    val = [I.V(i, nb[i]) for i in range(n)]; Jp = junk(I, nb)
    if len(nb[o]) > 1 or o in frozen(I, nb): return nb, False                                        # (O2)
    for j in range(n):                                                                               # (O1)
        if j != o and len(nb[j]) >= 2 and any(i != j and I.threat(i, val[i], nb[j]) for i in range(n)): return nb, False
    W = list(nb[o]) + Jp; F2 = set(frozen(I, nb))
    for q in range(n):                                                                               # (O3)
        if q == o: continue
        if (q in F2 or len(nb[q]) >= 2) and I.threat(q, val[q], W): return nb, False
    return nb, True


if __name__ == '__main__':
    sys.path.insert(0, HERE)
    from regimes import mechanism
    T = collections.Counter(); viol = []
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base); D = rec['D']
            p = [I.V(i, base[i]) for i in range(I.n)]
            found = False; found_own = False
            for k in D:
                for path, Ht in rings(I, base, k, J):
                    d = path[-1]; yd = base[d][0]
                    if d not in D: continue
                    Jk = [g for g in J if g in I.R[k] and g not in Ht]
                    for r in range(len(Jk) + 1):
                        for G in itertools.combinations(Jk, r):
                            H0 = (yd,) + G
                            if yd not in I.R[k] or I.V(k, H0) <= p[k]: continue
                            for o in range(I.n):
                                nb2, ok2 = ring_own(I, base, path, Ht, H0, o)
                                if not ok2: continue
                                T['RING-OWN (ring, owner) pairs'] += 1
                                if not sstar(I, nb2, o): viol.append(('OWN', rec['name'], rec['picks'], path, Ht, H0, o))
                                else: found_own = True
                            nb, ok = ring_red(I, base, path, Ht, H0)
                            if not ok: continue
                            T['RING-red rings'] += 1
                            if not sstar(I, nb, k): viol.append((rec['name'], rec['picks'], path, Ht, H0))
                            else: found = True
            mech, _ = mechanism(I, rec)
            T[('mechanism ' + mech, 'RING-red ring' if found else 'no RING-red ring')] += 1
            T[('mechanism ' + mech, 'RING-OWN ring' if found_own else 'no RING-OWN ring')] += 1
    print('$ python3 k4/oc1max_multi/ring.py', *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    print('RING-red / RING-OWN violations:', len(viol), viol[:5])
