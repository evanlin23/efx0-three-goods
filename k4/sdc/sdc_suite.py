"""SD-C and SD-C-R1 on every complete instance of the counterexample suite k4/suite/instances (all sizes).

    python3 k4/sdc/sdc_suite.py"""
import glob, json, os, time
import _paths
from sdsat import solve
from sdsat_r1 import solve_r1

if __name__ == '__main__':
    print('$ python3 k4/sdc/sdc_suite.py')
    c = [0, 0, 0]
    for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'k4/suite/instances/*.json'))):
        d = json.load(open(f))
        if not d.get('vals') or not d.get('sets'):
            continue
        sets, vals = d['sets'], d['vals']
        m = d.get('m') or 1 + max(max(s) for s in sets)
        t0 = time.time(); ok, _ = solve(sets, vals, m); ok1 = solve_r1(sets, vals, m)
        c[0] += 1; c[1] += (not ok); c[2] += (not ok1)
        print(f"{d.get('id', os.path.basename(f))}: n = {len(sets)}, m = {m}, SD-C {ok}, SD-C-R1 {ok1}, {time.time() - t0:.1f} s", flush=True)
    print('instances', c[0], 'SD-C failures', c[1], 'SD-C-R1 failures', c[2])
