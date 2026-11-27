"""One round of vertex-disjoint improving chains on the PW and POOL families (k4/ksens.md §4): one chain fails,
one round repairs, also with one absorber.  python3 k4/ksens/round_pw.py"""
import sys, random, time
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import _paths, ocsat, fam_pw, fam_ladder, fam_pool
rng = random.Random(3)
for f, W, r in [(3,2,4),(4,2,4),(3,3,5),(4,3,5),(4,3,6),(5,3,6),(5,4,7),(5,4,8),(6,4,7)]:
    bad = [0, 0, 0]; T = 10; t0 = time.time()
    for t in range(T):
        sets, vals, m = fam_pw.make(f, W, r, rng) if t else fam_ladder.clean(f, W, r)
        O = ocsat.OC(sets, vals, m); b = ocsat.bases_of(ocsat.sd(sets, vals, tuple(range(f + W)), m), f + W)
        bad[0] += not O.holds(b, chain='need')
        bad[1] += not O.holds(b, chain='need', multi=True)
        bad[2] += not O.holds(b, chain='need', multi=True, A=1)
        O.close()
    print('PW', (f, W, r), 'k', max(r + 1, f + 1), 'T', T, 'fail: one chain', bad[0], 'one round', bad[1], 'one round + one absorber', bad[2], '%.0fs' % (time.time() - t0), flush=True)
for f, r in [(4, 7), (5, 9)]:
    sets, vals, m = fam_pool.make(f, r, rng)
    O = ocsat.OC(sets, vals, m); b = ocsat.bases_of(ocsat.sd(sets, vals, tuple(range(2 * f)), m), 2 * f)
    print('POOL', (f, r), 'one chain', O.holds(b, chain='need'), 'one round', O.holds(b, chain='need', multi=True), 'round+A1', O.holds(b, chain='need', multi=True, A=1), flush=True)
