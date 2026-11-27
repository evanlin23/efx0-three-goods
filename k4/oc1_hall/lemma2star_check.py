"""Lemma 2* (k4/oc1_hall.md §6): under (G1) (bundles of non-holders other than o threaten nobody at base values) and
(G2) (no junk good is wanted), for EVERY owner o; and, with the fixed bundles of the non-holders counted as
threats that a holder's own slot good must answer, also where (G1) fails (frozen and multi-good owners included), the count of ohlib.deficit
(<= 0) agrees with the raw S* enumeration ohlib.shaped_completion.  At the picks and at every state one improving
chain reaches.  Also counts the states where (G1) or (G2) fails (Lemma 2* says nothing there).

    python3 k4/oc1_hall/lemma2star_check.py SRC
"""
import sys, os, itertools, collections, time, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import (Inst, picks, base_of_picks, bundles_of, frozen_set, deficit, shaped_completion, threatened,
                   wants_good)
from sdclib import Enc
from min_frozen import load
import de_free as DF
DF.CHAIN_ONLY = True

if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/lemma2star_check.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src, sys.argv):
        n = len(sets)
        if n > 4: continue
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); seen = set()
        for od in itertools.permutations(range(n)):
            Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); base = base_of_picks(I, Y)
            for tag, b in [('picks', base)] + [('after a chain', b2) for b2 in DF.moves(E, base)]:
                B = bundles_of(I, b); F = set(frozen_set(I, b)); J = [g for g in range(m) if b[g] < 0]
                pv = [I.val(i, B[i]) for i in range(n)]
                holders = [j for j in range(n) if len(B[j]) <= 1 and j not in F]
                if any(wants_good(I, B, i, g) for g in J for i in range(n)): C[tag + ': (G2) fails'] += 1; continue
                for o in range(n):
                    Q = [j for j in range(n) if j != o and j not in holders]
                    g1 = not any(threatened(I, i, pv[i], B[q]) for q in Q for i in range(n) if i != q)
                    C[tag + ': (G1) %s' % ('holds' if g1 else 'fails')] += 1
                    d = deficit(I, b, o, holders, Q, fixed_threats=True)[0]
                    ok = d is not None and d <= 0
                    ex = shaped_completion(I, b, o, holders)
                    C[tag + ': owner tests'] += 1
                    C[tag + ': owner tests, owner frozen or multi-good'] += o not in holders
                    if ok != ex:
                        C[tag + ': MISMATCH'] += 1
                        print('MISMATCH', tag, 'G1' if g1 else 'noG1', name, json.dumps((sets, vals)), b, o, ok, ex, flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
