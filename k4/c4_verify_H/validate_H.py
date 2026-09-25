"""SAT test vs C brute force on reachable states of H_t: every owner (and none), both conventions."""
import sys, time, random
from multiprocessing import Pool
from hcore import build_H
from lb4r import Inst, phase1_state, reach, all_needs, output_sat
from bfpy import bf_output
t = int(sys.argv[1]); q = int(sys.argv[2]); sample = int(sys.argv[3]) if len(sys.argv) > 3 else 0
agents, goods, v = build_H(t); inst = Inst(v)
s0, _ = phase1_state(inst, [])
levels = reach(inst, s0, q)
states = []
for d, lev in enumerate(levels):
    L = list(lev)
    if sample and d == q and len(L) > sample:
        L = random.Random(7).sample(L, sample)
    states += [(d, s) for s in L]
def job(ds):
    d, s = ds; needs = all_needs(inst, s); out = []
    for conv in ("bundle", "base"):
        for o in [None] + list(range(inst.n)):
            a, _ = output_sat(inst, s, o, conv, needs); b, leaves = bf_output(inst, s, o, conv)
            out.append((d, conv, o, a, b, leaves))
    return out
t0 = time.time()
with Pool(4) as p:
    res = [r for rs in p.map(job, states, chunksize=1) for r in rs]
mm = [r for r in res if r[3] != r[4]]
for d in range(q + 1):
    rd = [r for r in res if r[0] == d]
    print(f"H_{t} depth {d}: states={sum(1 for x in states if x[0]==d)} (state,owner,conv) cases={len(rd)} "
          f"SAT={sum(r[3] for r in rd)} brute SAT={sum(r[4] for r in rd)} mismatches={sum(1 for r in rd if r[3]!=r[4])} "
          f"max leaves={max(r[5] for r in rd)} total leaves={sum(r[5] for r in rd)}")
print("MISMATCHES:", mm[:5], f"time {time.time()-t0:.0f}s")
