"""Encoding B (enc_b.output_b, independent MILP) on every state of H_t reachable with <= q rotations, every
owner and no owner, both conventions. Usage: python3 run_encb.py t q"""
import sys, time
from multiprocessing import Pool
from hcore import build_H
from lb4r import Inst, phase1_state, up_run, reach
from enc_b import output_b
T = int(sys.argv[1]); Q = int(sys.argv[2])
agents, goods, v = build_H(T); inst = Inst(v)
def job(s):
    r = {"bundle": [], "base": []}
    for conv in ("bundle", "base"):
        for o in [None] + list(range(inst.n)):
            if output_b(v, s, o, conv):
                r[conv].append(o)
    return r
if __name__ == "__main__":
    t0 = time.time()
    s0, _ = phase1_state(inst, [])
    s1 = {up_run(inst, s0, p)[0] for p in ("shrink", "envyFree", "none")}
    assert s1 == {s0}
    levels = reach(inst, s0, Q)
    print(f"encoding B, H_{T}, q <= {Q}: states per depth {[len(l) for l in levels]}, total {sum(len(l) for l in levels)}", flush=True)
    first = {"bundle": None, "base": None}
    with Pool(4) as p:
        for d, lev in enumerate(levels):
            res = p.map(job, list(lev), chunksize=8)
            nb = sum(1 for r in res if r["bundle"]); nba = sum(1 for r in res if r["base"])
            for c, k in (("bundle", nb), ("base", nba)):
                if k and first[c] is None: first[c] = d
            print(f"depth {d}: {len(res)} states; states with an output: bundle={nb} base={nba} ({time.time()-t0:.0f}s)", flush=True)
    print(f"RESULT encB t={T} q<={Q}: least depth with an output: bundle={first['bundle']} base={first['base']}")
