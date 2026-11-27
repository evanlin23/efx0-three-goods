"""Residue B of Conjecture RF (k4/oc1_hall.md §24.7): RF starts Y' with one receiver d, two truly dangerous agents, and
w = d (u takes Y_d; d takes Y_u or a junk good).  For each B start of the certifier's complete n = 4 export: what d takes;
whether the two truly dangerous agents k1, k2 share two goods of J'; at the starts that complete at the picks, the
absorbers (ohlib.absorb_brute) and whether a frozen agent takes junk; at the others, which canonical chains k -> d
(k in D_T', d wanting Y_k; k takes a minimal improving T inside J' + {Y'_d}) leave a one-absorber completion (SAT) and
with which owners (raw, ohlib.absorb_brute).

    python3 k4/oc1_hall/rf_b.py
"""
import sys, os, json, gzip, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, absorb_brute, threatened, bundles_of, frozen_set, shaped_completion
from greedy_rules import apply_chain
from sdclib import Enc
from oc_absorb import extends_A
import _paths


def minimal_improving(I, k, pk, ground):
    imp = [H for r in range(1, len(ground) + 1) for H in itertools.combinations(ground, r) if I.val(k, H) > pk]
    return [H for H in imp if not any(set(K) < set(H) for K in imp)]


if __name__ == '__main__':
    d = json.load(gzip.open(os.path.join(_paths.ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    C = collections.Counter(); shown = collections.Counter()
    print('$ python3 k4/oc1_hall/rf_b.py', flush=True)
    for hg in d['hypergraphs']:
        sets = hg['sets']; m = 1 + max(max(s) for s in sets); seen = set()
        for st in hg['starts']:
            vals = st['vals']; I = Inst(sets, vals, m); E = Enc(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]; P0 = Picks(I, Y)
            for o in st['orders']:
                rf = [u] + [x for x in o if x != u]; Y2 = picks(I, rf)
                if (json.dumps(vals), Y2) in seen: continue
                seen.add((json.dumps(vals), Y2)); P = Picks(I, Y2); base = base_of_picks(I, Y2)
                U2 = [i for i in range(I.n) if i not in P.F and Y2[i] is not None]
                DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
                if len(U2) != 1 or len(DT) != 2: continue
                dd = U2[0]; C['B starts'] += 1
                took = 'Y_u' if Y2[dd] == Y[u] else 'junk'
                k1, k2 = DT
                shared = len([g for g in P.J if g in I.R[k1] and g in I.R[k2]])
                key = 'd takes %s; k1, k2 share %d junk goods' % (took, shared)
                C['  ' + key] += 1
                if extends_A(E, base, 1):
                    ab = absorb_brute(I, base, witness=True)
                    o_, X = ab
                    B = bundles_of(I, base); F2 = set(frozen_set(I, base))
                    fz = [j for j in range(I.n) if j != o_ and j in F2 and len(X[j]) > len(B[j])]
                    C['  %s: complete at the picks; first absorber found is %s; frozen slot used: %s' % (key, 'd' if o_ == dd else ('a D_T agent' if o_ in DT else 'other'), bool(fz))] += 1
                    continue
                reps = collections.Counter()
                for k in DT:
                    if not I.v[dd].get(Y2[k], 0) > P.pv[dd]: continue        # d must want Y_k for the chain k -> d
                    pool = [g for g in list(P.J) + [Y2[dd]] if g in I.R[k]]
                    for T in minimal_improving(I, k, P.pv[k], pool):
                        b2 = apply_chain(I, P, base, (k, dd), T)
                        if extends_A(E, b2, 1):
                            ow = absorb_brute(I, b2)
                            reps['chain k -> d repairs'] += 1
                            for x in ow: reps['owner ' + ('k' if x == k else ('d' if x == dd else ('the other D_T agent' if x in DT else 'other')))] += 1
                            B2 = bundles_of(I, b2); F3 = set(frozen_set(I, b2)); hold = [j for j in range(I.n) if len(B2[j]) <= 1 and j not in F3]
                            reps['S* owned by k after it'] += shaped_completion(I, b2, k, hold)
                C['  %s: one move needed; some chain k -> d (k in D_T\', minimal T) repairs' % key] += bool(reps['chain k -> d repairs'])
                for r in ('owner k', 'owner d', 'owner the other D_T agent', 'owner other', 'S* owned by k after it'):
                    C['  %s: ... %s (some repairing chain)' % (key, r)] += bool(reps[r])
                if not reps['chain k -> d repairs'] and shown[key] < 2:
                    shown[key] += 1
                    print('NO CHAIN k -> d REPAIRS', key, hg['list'], hg['idx'], json.dumps((sets, vals)), 'RF', rf, "Y'", Y2, 'd', dd, 'DT', DT, flush=True)
    for k_ in sorted(C): print(k_, C[k_])
