"""Conjecture RF's open residue (k4/oc1_hall.md §24.5; Lemma DEMOTE of k4/girth.md §7 on claude/k4-girth).  Data: every
failing (profile, picks, order) of the certifier's complete n = 4 export (results/k4_oc1max/two_move_starts_n4.json.gz).
For each failing order o with its unique receiver u, the RF order (u, o - u) gives the picks Y'.  Classified by
(|U'|, |D_T'|) (U' = unfrozen pick holders at Y', D_T' = dangerous agents threatened by J' alone at their pick value).
In the residue (|U'| = 1, |D_T'| in {0, 2}), with d the unique receiver of Y' and w the holder at Y of u's new good:
  OA     Y' has a one-absorber completion (SAT, oc_absorb.extends_A);
  S*d / S*w   an S* completion owned by d / by w (raw enumeration, ohlib.shaped_completion);
  OAd / OAw   a one-absorber completion with absorber d / w (raw enumeration, ohlib.absorb_brute; frozen slots allowed);
  ONE    one official move (de_free.moves) then a one-absorber completion (OC1 at Y').
Distinct (hypergraph, profile, Y') are counted once.

    python3 k4/oc1_hall/rf_residue.py [MAXHG]
"""
import sys, os, json, gzip, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, shaped_completion, absorb_brute, threatened, bundles_of, frozen_set
from sdclib import Enc
from oc_absorb import extends_A
import de_free as DF
import _paths
DF.CHAIN_ONLY = False

if __name__ == '__main__':
    maxhg = int(sys.argv[1]) if len(sys.argv) > 1 else 99
    d = json.load(gzip.open(os.path.join(_paths.ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    C = collections.Counter(); shown = collections.Counter()
    print('$ python3 k4/oc1_hall/rf_residue.py', *sys.argv[1:], flush=True)
    for hg in d['hypergraphs'][:maxhg]:
        sets = hg['sets']; m = 1 + max(max(s) for s in sets); seen = set()
        for st in hg['starts']:
            vals = st['vals']; I = Inst(sets, vals, m); E = Enc(sets, vals, m)
            Y = tuple(st['picks']); u = st['receivers'][0]
            for o in st['orders']:
                C['failing orders'] += 1
                rf = [u] + [x for x in o if x != u]; Y2 = picks(I, rf)
                key = (json.dumps(vals), Y2)
                if key in seen: continue
                seen.add(key); C['distinct RF starts'] += 1
                P = Picks(I, Y2); base = base_of_picks(I, Y2)
                U2 = [i for i in range(I.n) if i not in P.F and Y2[i] is not None]
                DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
                cls = 'R2 class (|U\'| >= 2)' if len(U2) >= 2 else ('U1 class (|U\'| = 1, |D_T\'| = 1)' if len(DT) == 1 else 'residue |U\'| = 1, |D_T\'| = %d' % len(DT))
                C[cls] += 1
                if not cls.startswith('residue'): continue
                dd = U2[0]; w = next(j for j in range(I.n) if Y[j] == Y2[u])
                oa = extends_A(E, base, 1)
                B = bundles_of(I, base); F2 = set(frozen_set(I, base))
                holders = [j for j in range(I.n) if len(B[j]) <= 1 and j not in F2]
                sd = shaped_completion(I, base, dd, holders); sw = shaped_completion(I, base, w, holders)
                ab = absorb_brute(I, base, owners=sorted({dd, w}))
                one = oa or any(extends_A(E, b2, 1) for b2 in DF.moves(E, base))
                for tag, ok in (('OA', oa), ('S*d', sd), ('S*w', sw), ('OAd', dd in ab), ('OAw', w in ab),
                                ('S*d or S*w', sd or sw), ('OAd or OAw', dd in ab or w in ab), ('ONE (OC1 at Y\')', one)):
                    C['  %s: %s' % (cls, tag)] += ok
                C['  %s: w == d' % cls] += (w == dd)
                if not (dd in ab or w in ab) and shown[cls] < 2:
                    shown[cls] += 1
                    print('NEITHER d NOR w ABSORBS', cls, hg['list'], hg['idx'], json.dumps((sets, vals)), 'RF order', rf, 'Y\'', Y2,
                          'd', dd, 'w', w, 'D\'', P.D, 'D_T\'', DT, 'OA', oa, 'ONE', one, flush=True)
        print('... hypergraph', hg['list'], hg['idx'], dict((k, v) for k, v in C.items() if not k.startswith('  ')), flush=True)
    for k in sorted(C): print(k, C[k])
