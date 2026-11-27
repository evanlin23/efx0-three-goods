"""Exactness checks for k4/matching/mlib.py (k4/matching.md §1).

For every distinct serial-dictatorship start of the chosen data (every order), and for the states one official move
reaches from it (sampled: every STRIDE-th move), test:
  (a) mlib.complete (pruned search, matching shortcut) against mlib.bf_complete (pruning-free brute force over every
      placement, raw EFX0), for every owner, both shapes (oa, ss), d = 0, 1, 2 dummy slots;
  (b) at states satisfying (G1), (G2): Lemma 2*'s matching form mlib.model_def(B, o) (min over kept-out sets H of the
      Hall deficiency |H| - nu(Gamma(H)), Konig-Ore checked) against the raw S* free-slot deficiency of owner o.

    python3 k4/matching/exact_check.py SRC [N SEED] [NMAX=4] [STRIDE=7]"""
import sys, os, itertools, collections, time
import _mpaths  # noqa: F401
from mlib import M, INF
from min_frozen import load

if __name__ == '__main__':
    src = sys.argv[1]; argv = sys.argv
    NMAX = int(os.environ.get('NMAX', '4')); STRIDE = int(os.environ.get('STRIDE', '7'))
    print('$ python3 k4/matching/exact_check.py', *sys.argv[1:], '(NMAX=%d STRIDE=%d)' % (NMAX, STRIDE), flush=True)
    C = collections.Counter(); t0 = time.time()
    for name, sets, vals, m in load(src, argv):
        n = len(sets)
        if n > NMAX: continue
        I = M(sets, vals, m, name); C['instances'] += 1
        starts = sorted(set(I.sd(o) for o in itertools.permutations(range(n))), key=str)
        for Y in starts:
            base = [[g] if g is not None else [] for g in Y]
            states = [('pick', base)] + [('move', b) for b in I.moves(base)[::STRIDE]]
            for kind, b in states:
                if len(I.junk(b)) > 6: C['skipped (|J| > 6)'] += 1; continue
                C['states ' + kind] += 1
                for shape in ('oa', 'ss'):
                    for o in range(n):
                        for d in (0, 1, 2):
                            a = I.complete(b, d, shape, [o]) is not None; z = I.bf_complete(b, d, shape, o)
                            C['(a) tests'] += 1
                            if a != z:
                                C['(a) MISMATCH'] += 1
                                print('MISMATCH (a)', name, sets, vals, 'state', b, shape, o, d, a, z, flush=True)
                if I.g1g2(b):
                    C['(b) states with (G1), (G2): ' + kind] += 1
                    for o in range(n):
                        md, H = I.model_def(b, o, konig=True); rd = I.deficiency(b, 'ss', [o])
                        C['(b) owner tests'] += 1
                        if md != rd:
                            C['(b) MISMATCH'] += 1
                            print('MISMATCH (b)', name, sets, vals, 'state', b, 'owner', o, 'model', md, 'raw', rd,
                                  flush=True)
                        else:
                            C['(b) agree, deficiency %s' % ('INF' if md >= INF else md)] += 1
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
