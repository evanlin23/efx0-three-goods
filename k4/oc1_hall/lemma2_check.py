"""Lemma 2 (k4/oc1_hall.md §4), constructively: at every distinct start and every unfrozen single-good owner o whose
hypotheses (G1), (G2), (G5'), (H3) hold, take the least-deficit witness (H, phi) of ohlib.deficit; when its count is
<= |N_1|, build the allocation by ohlib.lemma2_build (matched goods, the rest of H to unexposed holders, then
Theorem DT's moves) and check it with the raw EFX0 definition.  Also at the states one improving chain reaches.

    python3 k4/oc1_hall/lemma2_check.py SRC [chains]
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import (Inst, picks, base_of_picks, bundles_of, frozen_set, deficit, lemma2_build, efx0, threatened,
                   wants_good)
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True


def hypotheses(I, base, o):
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]; F = set(frozen_set(I, base))
    pv = [I.val(i, B[i]) for i in range(I.n)]
    N1 = [j for j in range(I.n) if j != o and len(B[j]) <= 1 and j not in F]
    Q = [j for j in range(I.n) if j != o and j not in N1]
    if any(threatened(I, i, pv[i], B[q]) for q in Q for i in range(I.n) if i != q): return None   # (G1)
    if any(wants_good(I, B, i, g) for g in J for i in range(I.n)): return None                    # (G2)
    if any(wants_good(I, B, i, g) for g in B[o] for i in N1): return None                         # (G5')
    for i in N1:                                                                                   # (H3)
        Bo = [g for g in B[o] if g in I.R[i]]
        if len(Bo) >= 2 and I.val(i, Bo) > pv[i]: return None
    return N1, Q


def check_state(I, base, C, tag):
    B = bundles_of(I, base)
    for o in range(I.n):
        hyp = hypotheses(I, base, o)
        if hyp is None: C[tag + 'owner: hypotheses fail'] += 1; continue
        N1, Q = hyp
        d, H, phi = deficit(I, base, o, N1, Q)
        C[tag + 'owner: hypotheses hold'] += 1
        if d is None or d > 0: continue
        X = lemma2_build(I, base, o, H, phi, N1)
        if X is None or not efx0(I, X) or any(sorted(set(b) & set(x)) != sorted(b) for b, x in zip(B, X)):
            C[tag + 'LEMMA 2 CONSTRUCTION FAILS'] += 1
            print('FAIL', tag, I.name, json.dumps((I.sets, I.vals)), 'base', base, 'o', o, 'H', H, phi, X, flush=True)
        else:
            C[tag + 'construction EFX0'] += 1


if __name__ == '__main__':
    src = sys.argv[1]; CH = 'chains' in sys.argv; C = collections.Counter(); t0 = time.time()
    argv = [a for a in sys.argv if a != 'chains']
    print('$ python3 k4/oc1_hall/lemma2_check.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, argv):
        n = len(sets)
        if n > 5: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y)
            check_state(I, base, C, 'picks: ')
            if CH:
                for b2 in DF.moves(E, base): check_state(I, b2, C, 'after a chain: ')
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
