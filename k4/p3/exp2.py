"""Lemmas MON2 and EXP2 (k4/p3.md section 6), checked on hard p <= 2 starts. Own code (p3lib, keep2, fk2).
For every hard start, every frozen k, P(k) = (k = x_0, ..., x_t = z), every improving H_0 inside (J + {Y_z}) & R_k,
with B' the bases after P(k) and W = J + {Y_z}:
  - MON2: the agents frozen at B' are frozen at the picks and off P(k); the unfrozen single-good holders at the picks
    other than z (the roots other than z) are still unfrozen single-good holders at B', with the same base; and
    x_1, ..., x_t are unfrozen single-good holders at B' (asserted);
  - EXP2: every x_i with 1 <= i < t that is not truly dangerous, does not value Y_z and does not value every junk good
    is not threatened by W at v(B'_{x_i}) (asserted), so it is unexposed for every kept-out set H.
It also counts how many agents of P(k) other than k are unexposed at W (H = {}).
    python3 k4/p3/exp2.py FILE [FILE ...]          (inputs as for k4/p3/fk2.py)
"""
import sys, os, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from p3lib import Inst
from oc1max import Checker
from keep2 import analyse, chain, state, threatened, frozen_at
from fk2 import starts, subsets

if __name__ == '__main__':
    cnt = collections.Counter()
    print('$ python3 k4/p3/exp2.py ' + ' '.join(sys.argv[1:]))
    for path in sys.argv[1:]:
        for sets, vals, m, Y in starts(path):
            I = Inst(sets, vals, m); K = Checker(I)
            base = tuple(frozenset([y]) for y in Y)
            if K.complete(base) is not None: K.close(); continue
            K.close()
            J, p, w, F, Dg, DT, EJ = analyse(I, list(Y))
            roots = [i for i in range(I.n) if i not in F]
            cnt['hard starts'] += 1
            for k in sorted(F):
                P = chain(w, k); z = P[-1]; t = len(P) - 1
                pool = [g for g in J if g in I.R[k]] + ([Y[z]] if Y[z] in I.R[k] else [])
                for H0 in subsets(pool, 1):
                    if I.val(k, H0) <= p[k]: continue
                    B = state(I, Y, P, H0); W = J + [Y[z]]
                    cnt['(chain, H0) tests'] += 1
                    fr = {q for q in range(I.n) if q != k and frozen_at(I, B, q)}
                    assert fr <= set(F) - set(P), 'MON2: new frozen agent'
                    assert all(B[r] == base[r] and r not in fr for r in roots if r != z), 'MON2: root changed'
                    assert all(len(B[x]) == 1 and x not in fr for x in P[1:]), 'MON2: chain agent frozen'
                    for i in range(1, t):
                        x = P[i]
                        hyp = x not in DT and Y[z] not in I.R[x] and not set(J) <= I.R[x]
                        exp = threatened(I, x, W, I.val(x, B[x]))
                        if hyp:
                            cnt['EXP2 cases'] += 1
                            assert not exp, ('EXP2 VIOLATION', sets, vals, Y, P, H0, x)
                        else:
                            cnt['middle chain agents outside EXP2: ' + ('exposed' if exp else 'unexposed')] += 1
                    ue = sum(1 for x in P[1:] if not threatened(I, x, W, I.val(x, B[x])))
                    cnt[f'unexposed agents of P(k) after k (H = empty): {ue} of {t}'] += 1
    for k in sorted(cnt): print(f'{k}: {cnt[k]}')
