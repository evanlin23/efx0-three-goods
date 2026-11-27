"""Theorem U (k4/oc1max_multi.md §3): at a hard perfect start with exactly one truly dangerous agent k (D_T = {k}),
let P be a longest canonical chain from k with head z, and H_0 inside the junk any improving set.  If every unfrozen
pick holder other than z is unthreatened by J at its pick value, and z is unfrozen after P or unthreatened by J at
p_z, then B' has an S* completion owned by k in which z (if unfrozen after P) or an unfrozen second wanter of the head's
new good takes the released pick Y_z.  Corollary U1: this holds for every longest chain when the start has exactly one
unfrozen pick holder.

Check at every hard perfect start with |D| >= 2 (raw EFX0, enumeration): for every longest chain meeting the
hypothesis and every improving H_0 (not only the minimal ones), the completion exists, with u = z when z is unfrozen
after P, else with u = some unfrozen second wanter; and, at the starts with one unfrozen pick holder, that z is unfrozen
after every longest chain.

    python3 k4/oc1max_multi/theorem_u1.py FILE.jsonl[.gz] [...]
"""
import sys, os, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from collect import records
from mmlib import Inst, base_from_picks, junk, frozen
from dred import canonical_chains, improving_sets, apply_chain
from lemma_b import truly_dangerous, keep_star_completion

if __name__ == '__main__':
    T = collections.Counter(); viol = []
    for fn in sys.argv[1:]:
        for rec in records(fn):
            I = Inst(rec['inst']['sets'], rec['inst']['vals'], rec['inst']['m'])
            base = base_from_picks(tuple(rec['picks'])); J = junk(I, base); D = rec['D']
            F = set(frozen(I, base))
            U = [i for i in range(I.n) if i not in F and base[i]]
            DT = truly_dangerous(I, base, D, J)
            T['starts'] += 1
            if len(DT) != 1: continue
            T['|D_T| = 1'] += 1
            k = DT[0]; chains = canonical_chains(I, base, k)
            L = max(len(c) for c in chains); ok = False; hyp = False
            EJ = [u for u in U if I.threat(u, I.V(u, base[u]), J)]
            for path in chains:
                if len(path) != L: continue
                z = path[-1]
                if any(u != z for u in EJ): continue
                for H0 in improving_sets(I, base, k, J, False):
                    nb = apply_chain(I, base, path, H0); F2 = set(frozen(I, nb))
                    if z in F2 and z in EJ: continue
                    hyp = True; T['(longest chain, H_0) pairs meeting the hypothesis'] += 1
                    if len(U) == 1 and z in F2: viol.append(('U1: head frozen', rec['name'], rec['picks'], path, H0))
                    if z not in F2: us = [z]
                    else:
                        a = nb[z][0]
                        us = [w for w in U if w not in path and I.v[w].get(a, 0) > I.V(w, nb[w])]
                        if not us: viol.append(('no second wanter', rec['name'], rec['picks'], path, H0)); continue
                    if keep_star_completion(I, nb, k, us[0], base[z][0]) is None:
                        viol.append(('no completion', rec['name'], rec['picks'], path, H0, us[0])); continue
                    ok = True
            if len(U) == 1: T['  one unfrozen pick holder'] += 1; T['  one unfrozen pick holder, repaired by Theorem U'] += ok
            T['  hypothesis of Theorem U met by some longest chain'] += hyp; T['  repaired by Theorem U'] += ok
    print('$ python3 k4/oc1max_multi/theorem_u1.py', *sys.argv[1:])
    for k in sorted(T): print(k, T[k])
    print('Theorem U1 violations:', len(viol), viol[:5])
