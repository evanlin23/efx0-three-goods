"""The hypergraph of Chaudhury-Garg-Mehlhorn's three-agent example (arXiv 2002.05119, §5, Table 3; values as in
kgen/charity/cgm_check.py on branch claude/kgen-charity, read there): relevant sets {0,1,2,3,5,6}, {0,2,3,4,6},
{4,5,6} (k = 6, n = 3, m = 7).  kcegar at D = 1 and D = 2 over every strict profile (the six-good agent by the LP
route), and the CGM values themselves (one chain from each maximum-matching start; ocsat and brute force).

    python3 k4/ksens/kcegar_cgm.py"""
import json, time
import _paths
import kcegar, ocsat, brute
from maxmatch import nu

SETS = [[0, 1, 2, 3, 5, 6], [0, 2, 3, 4, 6], [4, 5, 6]]
CGM = [{0: 8, 1: 2, 2: 12, 3: 2, 5: 17, 6: 1}, {0: 5, 2: 9, 3: 4, 4: 10, 6: 3}, {4: 9, 5: 10, 6: 2}]

if __name__ == '__main__':
    print('$ python3 k4/ksens/kcegar_cgm.py', flush=True); m, n = 7, 3
    vals = [[CGM[i][g] for g in SETS[i]] for i in range(n)]
    O = ocsat.OC(SETS, vals, m); I = brute.Inst(SETS, vals, m); v_ = nu(SETS, vals)
    for Y in ocsat.starts(SETS, vals, m):
        if sum(1 for g in Y if g is not None) != v_: continue
        b = ocsat.bases_of(Y, n); base = [frozenset([g]) if g is not None else frozenset() for g in Y]
        print('CGM values, start %s: picks complete (A=1) %s; one chain (A=1): ocsat %s, brute %s' % (
            Y, O.holds(b, chain='none', A=1), O.holds(b, chain='any', A=1),
            I.completes(base, 1) or any(I.completes(s, 1) for s in I.chains(base))), flush=True)
    for D in (1, 2):
        t = time.time(); C = kcegar.Cegar(SETS, D=D); r, w = C.run(time_limit=7200)
        print('every strict profile, D = %d: %s (%d iterations, %d LP calls, %.0f s)%s' % (
            D, r, C.iters, C.lpcalls, time.time() - t, (' ' + json.dumps(w)) if w else ''), flush=True)
        C.close()
