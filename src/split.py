import random, time
from core2 import rand_core, c2_sat
from exhaust5 import build
rng = random.Random(21); t0 = time.time()
rows = []
for n in (6, 7, 8, 9, 10):
    for m in range(n + 4, 2 * n):
        tot = f2 = f3 = 0
        for t in range(120 if n <= 8 else 60):
            trip = rand_core(n, m, rng, tries=40000)
            if trip is None: continue
            tot += 1
            if c2_sat(n, m, trip) is None:
                f2 += 1
                Sv, sel, _ = build(n, m, [tuple(sorted(T)) for T in trip], 'C3')
                if not Sv.solve(assumptions=[sel[(i,) + trip[i]] for i in range(n)]): f3 += 1
                Sv.delete()
        rows.append((n, m, tot, f2, f3))
        print(f"n={n:2d} m={m:2d} {'(=2n-1)' if m == 2*n-1 else '       '} cores={tot:3d} need a dump={f2:2d} one dump not enough={f3} ({time.time()-t0:.0f}s)", flush=True)
        if time.time() - t0 > 250: break
    if time.time() - t0 > 250: break
