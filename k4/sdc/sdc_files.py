import sys, json, random
from sdsat import solve
import _paths; R = _paths.ROOT + '/results/k4_de4/'
tot = bad = 0
for f in ['robust_failures.json', 'refute_lp_instance.json', 'refute_rob_instance.json', 'shed_failures_found.json',
          'shed2_near.json', 'unclean_cycles.json', 'v11_family_k2.json', 'v11_family_k3.json']:
    d = json.load(open(R + f))
    if isinstance(d, dict): d = d.get('instances', d.get('hypergraphs', []))
    k = 0
    for e in d:
        try:
            if isinstance(e, dict): sets, vals = e['sets'], e['vals']
            else: sets, vals = e[0], e[1]
            if not (isinstance(vals, list) and vals and isinstance(vals[0], list)): continue
            m = 1 + max(max(s) for s in sets)
        except Exception: continue
        ok, w = solve(sets, vals, m); tot += 1; k += 1
        if not ok: bad += 1; print('FAIL', f, json.dumps((sets, vals)), flush=True)
    print(f, k, flush=True)
print('total', tot, 'SD-C failures', bad)
