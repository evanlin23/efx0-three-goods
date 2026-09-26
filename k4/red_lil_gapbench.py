"""Run from a checkout of PR #53 (branch compute/k4-gap, which has k4/gap_bench.py and k4/gap_model.py): copy this file
there and run it from that repository root.
LIL (k4/c4min_reduce.md §5.3) tested with PR #53's independent model (k4/gap_model.py, k4/gap_bench.py).
f = 1 profiles only. Moves: one-agent re-pairings (two_agent_moves filtered to one changed pair), exchange-digraph
cycles (cycle_moves(general=True), which include rotations and path moves closed by a need edge), downgrade swaps.
Potential (r, -t, Lam)."""
import sys, os
sys.path.insert(0, 'k4'); import gap_bench as gb
def key(c): return (c.r, -c.t, c.Lam)
def lil(prof, c):
    if prof.f != 1 or c.completable: return None
    k0 = key(c)
    for mv in c.two_agent_moves():
        c2 = mv[-1]
        if sum(1 for y in c.free if c2.Q.get(y) != c.Q.get(y)) <= 1 and key(c2) > k0: return True
    for _, c2 in c.cycle_moves(general=True, keep=KEEP):
        if key(c2) > k0: return True
    for mv in c.downgrade_swaps():
        if key(mv[-1]) > k0: return True
    return False
KEEP = os.environ.get('KEEP') == '1'   # threat receivers may keep part of their own pair (#52, #53's keep=True)
cats = sys.argv[1].split(',')
every = int(sys.argv[2]) if len(sys.argv) > 2 else 1
res = gb.check(lil, scope='noncompl', catalogs=cats, name='LIL (r,-t,Lam), one-agent + cycles%s + downgrade' % (' with keep' if KEEP else ''), max_profiles=every)
print(res.summary())
for ce in res.counterexamples[:3]: print('counterexample', ce)
