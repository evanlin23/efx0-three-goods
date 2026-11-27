"""Attempt 'zero-move RKMAX' (attempts/k4-rkmax-zero-move.md): is the one-absorber completion at the picks of a
sigma-optimal maximum matching always available, with no move?  No.  Searches random strict MC2-class cores with n
agents for a sigma-optimal vector whose picks do not complete (rklib), and replays the smallest example found.
    python3 rk_zero_move.py N n SEED      # search
    python3 rk_zero_move.py replay        # replay the recorded example"""
import sys, random, json
from rklib import Prof, lexmax

EXS = [{'sets': [[0, 1, 2, 3], [0, 1, 2]], 'vals': [[14, 9, 25, 3], [25, 30, 35]]},                    # n = 2
       {'sets': [[0, 1, 2, 6], [1, 2, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]],
        'vals': [[1, 4, 8, 6], [2, 8, 7, 4], [4, 5, 8, 6], [4, 5, 8, 6]]}]                               # n = 4


def report(sets, vals):
    P = Prof(sets, vals); nu, mm = P.max_matchings(); best, O = lexmax(mm, P.sigma)
    out = []
    for Y in O:
        B = [frozenset([g]) for g in Y]
        out.append((Y, P.ranks(Y), P.one_absorber(B) is not None, P.oc1(Y)))
    return nu, best, out


if __name__ == '__main__':
    if sys.argv[1] == 'replay':
        for EX in EXS:
            nu, best, out = report(EX['sets'], EX['vals'])
            print('sets', EX['sets'], 'vals', EX['vals'], 'nu', nu, 'sigma-max', best)
            for Y, r, comp, oc in out: print('  sigma-optimal', Y, 'ranks', r, 'picks complete:', comp, 'OC1:', oc)
        sys.exit()
    sys.path.insert(0, '../sdc'); from oc1_mc2_rand import gen
    N, n, SEED = map(int, sys.argv[1:4]); rng = random.Random(SEED); found = 0
    t = -1; tried = 0
    while tried < N:
        t += 1
        try: sets, vals = gen(n, rng)
        except ValueError: continue          # the generator draws more goods than its pool at small n; redraw
        tried += 1; nu, best, out = report(sets, vals)
        if any(not comp for _, _, comp, _ in out):
            found += 1; print('FOUND', json.dumps({'sets': sets, 'vals': vals, 'opt': out}))
            if found >= 3: break
    print('searched', tried, 'found', found)
