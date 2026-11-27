"""Question W on the hypergraph of S'(sigma, k) (kgen/charity.md §6): can any real values on the relevant sets of
S'(sigma, k) make its stranded state (sigma - 1 goods out) the welfare maximum, i.e. strictly heavier than every
EFX0 allocation leaving fewer goods out?  Exact (z3 CEGAR, w_synth.run with a fixed state and support).

    python3 kgen/charity/w_synth_family.py SIGMA K [P|-] [VMAX|-] [CUTFILE]
P: the number of stranded goods to require (default sigma - 1); VMAX: integer values in 1..VMAX instead of reals."""
import sys, time
import w_synth
from stuck_family import build

if __name__ == '__main__':
    sigma, K = int(sys.argv[1]), int(sys.argv[2]); P = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '-' else sigma - 1
    VMAX = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != '-' else None
    print('$ python3 kgen/charity/w_synth_family.py', *sys.argv[1:], flush=True)
    I, X, pool, src, ch = build(sigma, K, own=True)
    # renumber goods: bundles first in agent order, then the pool, as w_synth expects nothing about order
    B = [sorted(X[a]) for a in range(I.n)]; Pl = sorted(pool)
    DUMP = sys.argv[5] if len(sys.argv) > 5 else None
    res = w_synth.run(I.n, K, P, None, 3000, fixed=(B, Pl, I.m, [set(I.R[a]) for a in range(I.n)]), vmax=VMAX,
                      dump=DUMP)
    print("S'(%d, %d) hypergraph, n %d, m %d, stranded %d: %s after %d cuts, %.1f s" % (sigma, K, I.n, I.m, len(Pl),
                                                                                res[0], res[1], res[2]), flush=True)
    if res[0] == 'FOUND':
        print('  values', [{g: str(x) for g, x in enumerate(row) if x} for row in res[3]], flush=True)
