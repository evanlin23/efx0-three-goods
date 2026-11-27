"""SLOT existence census (k4/oc1max_multi.md §10).  At every start whose first repairing mechanism is CAN-k (SLOT):

After a canonical chain P = (k, ..., z) with an improving H_0 inside the pool Pi = J + {Y_z}, owner k, an S* completion
with kept-out set H (inside J' = Pi - H_0) gives k the bundle W = Pi - H, whatever H_0 was.  Lemma M (plain: (G1) and
(G2) hold after a canonical chain, D-red 1) decides it.  Strategies, by the number of kept-out goods:
  HS   (Lemma HS, one slot at the head): H = {h}, z takes h; needs (S1) z unfrozen at B'; (S2) z admissible for h
       against W; (S3) every agent other than k and z unthreatened by W at its value at B'.
  ONE  one slot at any holder u (the same with u in place of z);
  MIN  the least |H| over all canonical chains, improving H_0 and owner k (Lemma M, by enumeration of H).
Also checked: Proposition HS-U1 (u = 1: the head of a longest chain is unfrozen at B'), and every HS / ONE allocation
by the raw EFX0 definition.  For starts without HS, the obstruction at the longest chains: for each h, which agents
W = Pi - h threatens that cannot be served (frozen at B', or holders other than the slot).

    python3 k4/oc1max_multi/slot_hs.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen, holders
from dred import canonical_chains, improving_sets, apply_chain
from regimes import mechanism
from mc import _match


def least_H(I, B, o, bound=None):
    """least |H| of a plain Lemma M certificate (S* completion with owner o, kept-out set H), or None"""
    n = I.n; J = junk(I, B); N1 = holders(I, B, o); b = [I.V(i, B[i]) for i in range(n)]
    for s in range(len(J) + 1):
        if bound is not None and s >= bound: return None
        for H in itertools.combinations(J, s):
            X = list(B[o]) + [g for g in J if g not in H]
            needy = [i for i in range(n) if i != o and I.threat(i, b[i], X)]
            if any(i not in N1 for i in needy) or len(H) > len(N1): continue
            adj = {h: [i for i in N1 if i not in needy or (h in I.R[i] and not I.threat(i, b[i] + I.v[i][h], X))] for h in H}
            nu, cover = _match(adj, list(H), needy)
            if cover and nu >= len(H): return s
    return None


def one_slot(I, base, path, H0, u_only=None):
    """[(h, u)]: one kept-out good h in J' given to holder u, all other agents (k, u excepted) unthreatened by Pi - h"""
    k, z = path[0], path[-1]; nb = apply_chain(I, base, path, H0); J1 = junk(I, nb)
    Pi = J1 + list(nb[k]); hs = holders(I, nb, k); val = [I.V(i, nb[i]) for i in range(I.n)]; out = []
    for h in J1:
        W = [g for g in Pi if g != h]
        bad = [i for i in range(I.n) if i != k and I.threat(i, val[i], W)]
        for u in ([u_only] if u_only is not None else hs):
            if u not in hs or any(i != u for i in bad): continue
            if u in bad and not (h in I.R[u] and not I.threat(u, val[u] + I.v[u][h], W)): continue
            X = [list(b) for b in nb]; X[u].append(h); X[k] = W
            out.append((h, u, I.efx0(X)))
    return nb, out


def role(I, base, nb, i, k, z, D, DT):
    F2 = set(frozen(I, nb))
    r = 'z' if i == z else ('D_T' if i in DT else 'D-D_T' if i in D else 'other')
    return r + (' frozen' if i in F2 or len(nb[i]) > 1 else ' holder')


if __name__ == '__main__':
    from lemma_b import truly_dangerous
    T = collections.Counter(); viol = []; ex = {}; obst = collections.Counter()
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            mech, DT = mechanism(I, rec)
            if mech != 'CAN-k': continue
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base); D = rec['D']; F = set(frozen(I, base))
            U = [i for i in range(I.n) if i not in F and base[i]]
            key = ('u=%d' % min(len(U), 3), '|D_T|=%d' % min(len(DT), 2))
            st = set(); mins = []; fails = collections.Counter()
            for k in D:
                ch = canonical_chains(I, base, k)
                if not ch: continue
                L = max(len(c) for c in ch)
                for path in ch:
                    z = path[-1]
                    for H0 in improving_sets(I, base, k, J + list(base[z]), True):
                        nb, hs = one_slot(I, base, path, H0, u_only=z)
                        if len(U) == 1 and len(path) == L:
                            T['HS-U1: longest chains at u = 1'] += 1
                            if z in frozen(I, nb): T['HS-U1 VIOLATION (head frozen at B\')'] += 1
                        for h, u, ok in hs:
                            if not ok: viol.append(('HS', rec['name'], path, H0, h))
                            else: st.add('HS'); st.add('HS longest') if len(path) == L else None
                        nb, os1 = one_slot(I, base, path, H0)
                        for h, u, ok in os1:
                            if not ok: viol.append(('ONE', rec['name'], path, H0, h, u))
                            else: st.add('ONE')
                        if len(path) == L and not hs:
                            Pi = junk(I, nb) + list(nb[k]); val = [I.V(i, nb[i]) for i in range(I.n)]
                            for h in junk(I, nb):
                                W = [g for g in Pi if g != h]
                                bad = tuple(sorted(set(role(I, base, nb, i, k, z, D, DT) for i in range(I.n)
                                                       if i != k and I.threat(i, val[i], W) and
                                                       not (i == z and h in I.R[z] and not I.threat(z, val[z] + I.v[z][h], W)))))
                                fails[bad] += 1
            # least |H| by plain Lemma M over canonical chains (owner k)
            best = None
            for k in D:
                for path in canonical_chains(I, base, k):
                    for H0 in improving_sets(I, base, k, J + list(base[path[-1]]), True):
                        nb = apply_chain(I, base, path, H0); s0 = least_H(I, nb, k, best)
                        if s0 is not None and (best is None or s0 < best): best = s0
            T[key + ('starts',)] += 1
            for s in st: T[key + (s,)] += 1
            T[key + ('least |H| (owner k, canonical) <= %s' % best,)] += 1
            if 'HS' not in st:
                for b, c in fails.items(): obst[b] += 1
                if key not in ex or (I.n, I.m) < ex[key][0]: ex[key] = ((I.n, I.m), rec, dict(fails))
    print('$ python3 k4/oc1max_multi/slot_hs.py', *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    print('HS / ONE violations (conditions hold, allocation not EFX0):', len(viol), viol[:5])
    print('obstructions to HS at longest chains (starts without HS; per h: roles of the unservable threatened agents):')
    for b, c in sorted(obst.items(), key=lambda x: -x[1]): print('  ', c, b)
    for k, ((n, m), r, f) in sorted(ex.items()):
        print('smallest without HS', k, r['name'], 'n=%d m=%d' % (n, m), json.dumps([r['inst']['sets'], r['inst']['vals']]),
              'picks', r['picks'], 'obstructions', f)
