"""LB4^r (index insertion, tau = []) on H_t: exhaustive over every state reachable with <= q rotations,
every owner (and no owner), both owner-needs conventions. Usage: python3 run_H.py t q [--workers W]"""
import sys
import time
from multiprocessing import Pool
from hcore import build_H
from lb4r import Inst, phase1_state, up_run, reach, all_needs, output_sat, output_check, omega, base_of

T = int(sys.argv[1])
Q = int(sys.argv[2])
W = 4
BACKEND = "milp"
for a in sys.argv[3:]:
    if a.startswith("--workers="):
        W = int(a.split("=")[1])
    if a.startswith("--backend="):
        BACKEND = a.split("=")[1]

agents, goods, v = build_H(T)
inst = Inst(v)


def test_state(s):
    """Return (owners that succeed under 'bundle', under 'base')."""
    needs = all_needs(inst, s)
    res = {"bundle": [], "base": []}
    for conv in ("bundle", "base"):
        for o in [None] + list(range(inst.n)):
            ok, X = output_sat(inst, s, o, conv, needs, want_model=True, backend=BACKEND)
            if ok:
                assert output_check(inst, s, o, X, conv, needs), "model fails literal check"
                res[conv].append(o)
    return res


def describe(s):
    base, pick, marked = s
    out = []
    for i in range(inst.n):
        B = [goods[g] for g in range(inst.m) if base[g] == i]
        out.append(f"{agents[i]}{'*' if marked[i] else ''}:{{{','.join(B)}}}")
    return " ".join(out)


if __name__ == "__main__":
    t0 = time.time()
    s0, run = phase1_state(inst, [])
    print(f"H_{T}: n={inst.n} m={inst.m} backend={BACKEND}")
    print("Phase 1 (agent, pick, step):", " ".join(f"{agents[x]}->{goods[f] if f is not None else '-'}({k})" for x, f, k in run))
    needs0 = all_needs(inst, s0)
    print("needs after Phase 1:", {agents[i]: sorted(goods[g] for g in needs0[i]) for i in range(inst.n) if needs0[i]})
    print("junk:", sorted(goods[g] for g in range(inst.m) if s0[0][g] == -1), "omega =", omega(inst, s0))
    s1 = None
    for pol in ("shrink", "envyFree", "none"):
        sp, steps = up_run(inst, s0, pol)
        print(f"policy {pol}: upgrades {steps}; state unchanged: {sp == s0}")
        assert s1 is None or sp == s1
        s1 = sp
    levels = reach(inst, s1, Q)
    cum = 0
    for d, lev in enumerate(levels):
        cum += len(lev)
        print(f"depth {d}: {len(lev)} new states, {cum} states with <= {d} rotations", flush=True)
    print(f"reachability done in {time.time() - t0:.1f}s", flush=True)
    first = {"bundle": None, "base": None}
    with Pool(W) as pool:
        for d, lev in enumerate(levels):
            states = list(lev.keys())
            results = pool.map(test_state, states, chunksize=max(1, len(states) // (8 * W) or 1))
            nb = sum(1 for r in results if r["bundle"])
            nbase = sum(1 for r in results if r["base"])
            om = [omega(inst, s) for s in states]
            print(f"depth {d}: states={len(states)} omega in [{min(om)},{max(om)}] | states with an output: "
                  f"bundle={nb} base={nbase}  ({time.time() - t0:.1f}s)", flush=True)
            for conv, cnt in (("bundle", nb), ("base", nbase)):
                if cnt and first[conv] is None:
                    first[conv] = d
                    k = next(i for i, r in enumerate(results) if r[conv])
                    s = states[k]
                    print(f"  first success ({conv}) at depth {d}: owners "
                          f"{[agents[o] if o is not None else None for o in results[k][conv]]}")
                    print("   state:", describe(s))
                    # path
                    path = []
                    cur, dd = s, d
                    while dd > 0:
                        par, desc = levels[dd][cur]
                        c, O = desc
                        path.append(f"chain {[agents[a] for a in c]} O={[goods[g] for g in O]}")
                        cur, dd = par, dd - 1
                    print("   path:", " ; ".join(reversed(path)))
    print(f"RESULT t={T} q<={Q}: least depth with an output: bundle={first['bundle']} base={first['base']} "
          f"(Proposition H bound ceil(2t/3) = {-(-2 * T // 3)}); total {time.time() - t0:.1f}s")
