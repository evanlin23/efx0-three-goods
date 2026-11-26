"""(Superseded by refute_oc1_r1.py, which includes this case as PW436.)  OC1 (and OC) restricted to R1-priority orders fail at k = 7 (k4/ksens.md §4): PW(4, 3, 6) with clean values,
the R1-priority service order (x_1, w_1, x_2, x_3, x_4, w_2, w_3).  Checks, from the picks:
  1. ocsat.py (one chain encoded in SAT) and ocseq.py (a separately written encoding of c chains), both on sdclib's
     EFX0 clauses;
  2. brute.py, independent of SAT: every improving chain enumerated by depth-first search from the definition, and the
     completion of every resulting state decided by backtracking over the placement of the junk against the raw EFX0
     definition (brute.Inst.completes_bt; checked against the full enumeration on PW5, 38,286 comparisons).

    python3 k4/ksens/refute_oc1_r1_k7.py"""
import json, time
import _paths
import ocsat, ocseq, brute, fam_ladder
from r1_pw import sd_r1

if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_oc1_r1_k7.py', flush=True)
    sets, vals, m = fam_ladder.clean(4, 3, 6); n = 7; order = (0, 4, 1, 2, 3, 5, 6)
    Y = tuple(sd_r1(sets, vals, order, m)); b = ocsat.bases_of(Y, n)
    print('PW(4,3,6)', json.dumps((sets, vals)), 'R1 order', order, 'picks', Y, flush=True)
    O = ocsat.OC(sets, vals, m); Q = ocseq.Seq(sets, vals, m)
    r = {'ocsat oc': O.holds(b, chain='any'), 'ocsat oc1': O.holds(b, chain='any', A=1),
         'ocseq <=1 chain free': Q.holds(b, 1), 'ocseq <=1 chain A=1': Q.holds(b, 1, 1), 'ocseq <=2 chains free': Q.holds(b, 2)}
    print('SAT:', r, flush=True)
    I = brute.Inst(sets, vals, m); t0 = time.time()
    base = [frozenset([g]) if g is not None else frozenset() for g in Y]
    ch = I.chains(base); print('brute force: %d distinct one-chain states (%.0f s)' % (len(ch), time.time() - t0), flush=True)
    c0 = I.completes_bt(base); c0a = I.completes_bt(base, 1)
    free = sum(1 for s in ch if I.completes_bt(s)); one = sum(1 for s in ch if I.completes_bt(s, 1))
    print('brute force: picks complete free %s, one absorber %s; states with a free completion %d, with a one-absorber '
          'completion %d (%.0f s)' % (c0, c0a, free, one, time.time() - t0), flush=True)
    assert not r['ocsat oc'] and not r['ocsat oc1'] and not r['ocseq <=1 chain free'] and r['ocseq <=2 chains free']
    assert not c0 and free == 0 and one == 0
    print('OK: OC and OC1 fail from an R1-priority order at k = 7; two chains suffice')
