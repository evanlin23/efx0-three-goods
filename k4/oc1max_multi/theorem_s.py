"""Theorem S (k4/oc1max_multi.md §10): Theorem U with a junk good kept out.

Y a perfect start, k in D, P = (k, ..., z) a longest canonical chain from k, h in J, W = (J - {h}) + {Y_z}.
Hypotheses (all at the picks, except that z is P's head):
  (S-a) v_k(W) > p_k                       (an improving H_0 inside W exists);
  (S-b) W threatens no agent of D - {k} at its pick value;
  (S-c) W threatens no unfrozen pick holder other than z at its pick value;
  (S-d) z values no junk good other than h  (relaxed, chain-level (S-d'): W does not threaten z at its value in the
        allocation below).
With h = Y_z (W = J) the relaxed form is Theorem U (§3); the third census line is the union.
Conclusion: for every improving H_0 inside W, after P the allocation  k: W,  z: {a, h} if z is unfrozen after P,
otherwise w: {Y_w, h} for an unfrozen wanter w of a = Y_{x_{t-1}},  everyone else his state good, is EFX0 (an S*
completion with owner k and H = {h}).

The census checks the conclusion with the raw EFX0 definition for every (k, longest P, h, minimal H_0) meeting the
hypotheses, at every start, and counts the starts covered, by regime (regimes.mechanism).

    python3 k4/oc1max_multi/theorem_s.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen
from dred import canonical_chains, improving_sets, apply_chain
from regimes import mechanism


def s_cases(I, base, D, relaxed=False, pick_too=False):
    """yield (k, P, h, H0, allocation or None) for every case meeting (S-a)-(S-d) (or (S-d'))"""
    J = junk(I, base); F = set(frozen(I, base)); n = I.n; p = [I.V(i, base[i]) for i in range(n)]
    U = [i for i in range(n) if i not in F and base[i]]
    for k in D:
        ch = canonical_chains(I, base, k)
        if not ch: continue
        L = max(len(c) for c in ch)
        for P in ch:
            if len(P) != L: continue
            z = P[-1]; Yz = base[z][0]
            for h in J + ([Yz] if pick_too else []):
                W = [g for g in J + [Yz] if g != h]
                if I.V(k, W) <= p[k]: continue                                                  # (S-a)
                if any(I.threat(d, p[d], W) for d in D if d != k): continue                    # (S-b)
                if any(I.threat(u, p[u], W) for u in U if u != z): continue                    # (S-c)
                if not relaxed and any(g != h for g in J if g in I.R[z]): continue             # (S-d)
                for H0 in improving_sets(I, base, k, W, True):
                    nb = apply_chain(I, base, P, H0); F2 = set(frozen(I, nb))
                    X = [list(b) for b in nb]; X[k] = list(W)
                    if z not in F2: X[z].append(h)
                    else:
                        a = base[P[-2]][0]; val = [I.V(i, nb[i]) for i in range(n)]
                        ws = [w for w in range(n) if w != z and I.v[w].get(a, 0) > val[w]]
                        ws = [w for w in ws if w not in F2 and len(nb[w]) == 1]
                        if not ws: yield k, P, h, H0, None, 'no unfrozen wanter'; continue
                        X[ws[0]].append(h)
                    if relaxed and I.threat(z, I.V(z, X[z]), W): continue                       # (S-d')
                    yield k, P, h, H0, X, ('z takes h' if z not in F2 else 'wanter takes h')


if __name__ == '__main__':
    T = collections.Counter(); viol = []; ex = {}
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); D = rec['D']
            mech, DT = mechanism(I, rec); T[('starts', mech)] += 1; T['starts'] += 1
            for relaxed, pt in ((False, False), (True, False), (True, True)):
                tag = ("(S-d'), h in J + {Y_z} (Theorem U and S)" if pt else "(S-d')") if relaxed else '(S-d)'; cov = False
                for k, P, h, H0, X, how in s_cases(I, base, D, relaxed, pt):
                    T[(tag, 'cases', how)] += 1
                    if X is None or not I.efx0(X): viol.append((tag, rec['name'], rec['picks'], P, h, H0, how)); continue
                    cov = True
                if cov:
                    T[(tag, 'covered', mech)] += 1; T[(tag, 'covered')] += 1
                elif pt and mech == 'CAN-k':      # the SLOT residue: least kept-out set of a canonical repair, owner k
                    from slot_hs import least_H, one_slot
                    J = junk(I, base); best = None; one_head = False
                    for k in D:
                        for P in canonical_chains(I, base, k):
                            for H0 in improving_sets(I, base, k, J + list(base[P[-1]]), True):
                                nb = apply_chain(I, base, P, H0); s0 = least_H(I, nb, k, best)
                                if s0 is not None and (best is None or s0 < best): best = s0
                                one_head |= bool(one_slot(I, base, P, H0, P[-1])[1])
                    T[('SLOT residue', 'least |H| = %s' % best, 'head slot (Lemma HS) at some chain' if one_head else 'no head slot')] += 1
                    size = (I.n, I.m)
                    if ('res', best) not in ex or size < ex[('res', best)][0]: ex[('res', best)] = (size, rec['name'], rec['picks'])
                    if mech in ('CAN-k', 'ED') and (tag, mech) not in ex: ex[(tag, mech)] = rec['name']
    print('$ python3 k4/oc1max_multi/theorem_s.py', *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    print('violations (hypotheses hold, allocation not EFX0 or no holder):', len(viol), viol[:5])
    print('examples', ex)
