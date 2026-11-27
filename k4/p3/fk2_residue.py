"""What Proposition FK2 leaves (k4/p3.md section 6): at the hard starts where no jump chain satisfies FK2's hypotheses
(k4/p3/fk2.py), which hypothesis fails on the jump chains that repair anyway, and who causes it.
For each repairing jump chain and each variant (A: H = {}; B: H = {Y_{z_k}}), the failed conditions:
  - C: some agent frozen after the chain is threatened (by W = (J - G) + {Y_{z_k}}, or J - G for B) at its pick value;
       the agent is classified as truly dangerous (in D_T) or not (pick-dangerous, threatened through Y_{z_k});
  - Q: some entry d_i (i >= 2) is threatened at its new base value (only possible when d_k is a root);
  - N: some single-good holder other than d_1 (and z_k for B) is crowded by H_0; the holder is classified as truly
       dangerous (in D_T, unfrozen by the chain), junk-exposed at the picks (in E_J), or other;
  - shape (B only): Y_{z_k} in H_0, or P(d_k) trivial.
A start is classified by its minimal failure sets over its repairing chains and both variants (all of them, with the
least k at which each occurs).
    python3 k4/p3/fk2_residue.py FILE [FILE ...]      (inputs as for k4/p3/fk2.py)
"""
import sys, os, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker
from keep2 import analyse, threatened, frozen_at
from fk2 import starts, jump_chains, crowded, hypotheses


def failures(I, Y, J, p, DT, EJ, d1, S, G, H0, B):
    zk = S[-1][-1]; n = I.n
    Fr = [q for q in range(n) if q != d1 and len(B[q]) == 1 and frozen_at(I, B, q)]
    holders = [u for u in range(n) if u != d1 and len(B[u]) == 1 and u not in Fr]
    multi = [q for q in range(n) if q != d1 and len(B[q]) >= 2]
    JG = [g for g in J if g not in G]
    res = {}
    for var, W, skip in (('A', JG + [Y[zk]], set()), ('B', JG, {zk})):
        f = set()
        if var == 'B' and (Y[zk] in H0 or len(S[-1]) < 2): f.add('shape')
        for q in Fr:
            if threatened(I, q, W, p[q]): f.add('C:' + ('D_T' if q in DT else 'pick-dangerous'))
        for q in multi:
            if threatened(I, q, W, I.val(q, B[q])): f.add('Q')
        for u in holders:
            if u not in skip and crowded(I, B, u, H0): f.add('N:' + ('D_T' if u in DT else 'E_J' if u in EJ else 'other'))
        res[var] = frozenset(f)
    return res


if __name__ == '__main__':
    cnt = collections.Counter(); ex = {}
    print('$ python3 k4/p3/fk2_residue.py ' + ' '.join(sys.argv[1:]))
    for path in sys.argv[1:]:
        for sets, vals, m, Y in starts(path):
            I = Inst(sets, vals, m); K = Checker(I)
            base = tuple(frozenset([y]) for y in Y)
            if K.complete(base) is not None: K.close(); continue
            J, p, w, F, Dg, DT, EJ = analyse(I, list(Y))
            chs = list(jump_chains(I, Y, J, p, w, F))
            if any(hypotheses(I, Y, J, p, *c) for c in chs): K.close(); continue
            cnt['residue starts'] += 1
            fs = {}
            for c in chs:
                if K.complete(tuple(c[4])) is None: continue
                for var, f in failures(I, Y, J, p, DT, EJ, *c).items():
                    fs[f] = min(fs.get(f, 99), len(c[1]))
            if not fs: cnt['no jump chain repairs'] += 1; continue
            mins = sorted((sorted(f), fs[f]) for f in fs if not any(g < f for g in fs))
            lab = ' | '.join('{' + ', '.join(f) + '}' + (f' k={k}' if k > 1 else '') for f, k in mins)
            cnt['least failure: ' + lab] += 1
            key = (I.n, I.m)
            if lab not in ex or key < ex[lab][0]: ex[lab] = (key, {'sets': sets, 'vals': vals, 'picks': Y, 'D': sorted(Dg), 'D_T': sorted(DT), 'E_J': sorted(EJ)})
            K.close()
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
    for k, v in sorted(ex.items()): print('smallest with', k, json.dumps(v[1]))
