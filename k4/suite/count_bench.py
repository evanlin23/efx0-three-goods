"""COUNT and SIMPLE over #53's gap catalogues with #53's bench (k4/gap_bench.py, read from k4/suite/.cache/gapbench, a
git archive of compute/k4-gap at 245040b: `git archive 245040b k4 results/k4_gap results/k4_certs_*.json.gz | tar -x -C
k4/suite/.cache/gapbench`). SIMPLE: some configuration at a min-frozen key has a valid owner with C empty. COUNT: some
pool-optimal configuration has r' > |D| (D = free owners that threaten a frozen agent), a certificate for SIMPLE.
usage: python3 k4/suite/count_bench.py k4/suite/.cache/gapbench CATALOG.json.gz [MAX_PROFILES]"""
import sys, time
B = sys.argv[1]
sys.path.insert(0, B + '/k4')
import gap_bench as gb
def count(prof, cfgs):
    for c in cfgs:
        if not c.pool_optimal: continue
        rp = sum(1 for y in c.free if c.robust(y))
        D = sum(1 for o in c.free if any(c.threatens(o, x) for x in c.frozen))
        if rp > D: return True
    return False
def simple(prof, cfgs): return any(c.simple for c in cfgs)
t0 = time.time()
cats = [B + '/results/k4_gap/' + f for f in sys.argv[2].split(',')]
mp = int(sys.argv[3]) if len(sys.argv) > 3 and sys.argv[3] != '0' else None
recs = None
for name, fn in (('SIMPLE', simple), ('COUNT', count)):
    res = gb.check(fn, scope='profile', catalogs=cats, name=name, max_profiles=mp, confirm=2)
    print(res.summary().split('\n')[0]); print('  time', round(time.time() - t0))
    for ce in res.counterexamples[:4]:
        p = ce[0]; print('  CE', p.sets, [[p.v[i][g] for g in p.sets[i]] for i in range(p.n)])
