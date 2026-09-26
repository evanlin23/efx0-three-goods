import sys, time, random
from multiprocessing import Pool
from hcore import build_H
from lb4r import Inst, phase1_state, reach
from bfpy import bf_output
from enc_b import output_b
t = int(sys.argv[1]); q = int(sys.argv[2]); sample = int(sys.argv[3]) if len(sys.argv) > 3 else 0
agents, goods, v = build_H(t); inst = Inst(v)
s0, _ = phase1_state(inst, []); levels = reach(inst, s0, q)
states = []
for d, lev in enumerate(levels):
    L = list(lev)
    if sample and d == q and len(L) > sample: L = random.Random(9).sample(L, sample)
    states += [(d, s) for s in L]
def job(ds):
    d, s = ds; out = []
    for conv in ("bundle", "base"):
        for o in [None] + list(range(inst.n)):
            out.append((d, output_b(v, s, o, conv), bf_output(inst, s, o, conv)[0]))
    return out
with Pool(2) as p:
    res = [r for rs in p.map(job, states, chunksize=1) for r in rs]
for d in range(q + 1):
    rd = [r for r in res if r[0] == d]
    print(f"H_{t} depth {d}: cases={len(rd)} encB SAT={sum(r[1] for r in rd)} brute SAT={sum(r[2] for r in rd)} mismatches={sum(r[1]!=r[2] for r in rd)}")
