"""Lemma WG (worthless goods; k4/oc1max_multi.md §13) on the SLOT residue (SLOT2) and the RING residue.

Setting: B satisfies (G1), (G2) (e.g. the state after a canonical chain), o is the owner, J the junk, i an agent other
than o.  Put H = J - R_i (the junk goods worth 0 to i) and X = B_o + (J & R_i).  Suppose
  (W1) B_o is inside R_i (so X is inside R_i, and EFX0's least-good removal costs i its cheapest good of X);
  (W2) X threatens no agent other than o at its value at B (for i: v_i(X) - min_X v_i <= b_i);
  (W3) there are |H| distinct holders (agents other than o with at most one base good nobody wants).
Then B has an S* completion with owner o and kept-out set H: the holders take one good of H each, o takes X.
(Lemma M with no needy agent: every holder accepts every good.)

Census: at every start of the SLOT residue (first mechanism CAN-k, outside Theorems U and S) and of RING (mechanism
ED), whether some canonical chain from some k in D with a minimal improving H_0 and some i meets (W1)-(W3) (owner k);
every case is checked with the raw EFX0 definition.

    python3 k4/oc1max_multi/wg.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, holders
from dred import canonical_chains, improving_sets, apply_chain
from regimes import mechanism
from theorem_s import s_cases


def wg_cases(I, B, o):
    J = junk(I, B); N1 = holders(I, B, o); b = [I.V(j, B[j]) for j in range(I.n)]
    for i in range(I.n):
        if i == o or not set(B[o]) <= I.R[i]: continue                                       # (W1)
        H = [g for g in J if g not in I.R[i]]
        if not H: continue
        X = list(B[o]) + [g for g in J if g in I.R[i]]
        if any(I.threat(j, b[j], X) for j in range(I.n) if j != o): continue                 # (W2)
        if len(H) > len(N1): continue                                                         # (W3)
        A = [list(x) for x in B]; A[o] = X
        for g, u in zip(H, N1): A[u].append(g)
        yield i, H, A


if __name__ == '__main__':
    T = collections.Counter(); viol = []; ex = {}
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            mech, DT = mechanism(I, rec)
            if mech not in ('CAN-k', 'ED'): continue
            base = base_from_picks(tuple(rec['picks'])); D = rec['D']; J = junk(I, base)
            if mech == 'CAN-k':
                cov = any(X is not None and I.efx0(X) for *_, X, how in s_cases(I, base, D, True, True))
                if cov: continue
            leaf = 'SLOT2' if mech == 'CAN-k' else 'RING2'
            got = False
            for k in D:
                for P in canonical_chains(I, base, k):
                    for H0 in improving_sets(I, base, k, J + list(base[P[-1]]), True):
                        nb = apply_chain(I, base, P, H0)
                        for i, H, A in wg_cases(I, nb, k):
                            T[(leaf, 'WG cases')] += 1
                            if not I.efx0(A): viol.append((rec['name'], P, H0, i, H))
                            else: got = True
            T[(leaf, 'starts')] += 1; T[(leaf, 'covered by Lemma WG' if got else 'not covered')] += 1
            if not got:
                sz = (I.n, I.m)
                if leaf not in ex or sz < ex[leaf][0]: ex[leaf] = (sz, rec['name'], rec['picks'])
    print('$ python3 k4/oc1max_multi/wg.py', *sys.argv[1:])
    for k in sorted(T, key=str): print(k, T[k])
    print('violations (W1)-(W3) hold, allocation not EFX0:', len(viol), viol[:5])
    print('smallest not covered:', ex)
