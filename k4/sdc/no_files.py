"""Conjecture NO on the instances that refuted DE4's candidates (results/k4_de4/*.json) and on H_t, HH_t.

    python3 k4/sdc/no_files.py"""
import os, sys, json
import _paths
from sdc_no import no_holds
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
import adaptive_H as AH
from sdc_ht import build_hh

if __name__ == '__main__':
    print('$ python3 k4/sdc/no_files.py')
    R = os.path.join(_paths.ROOT, 'results', 'k4_de4')
    tot = bad = 0
    for f in ['robust_failures.json', 'refute_lp_instance.json', 'refute_rob_instance.json', 'shed_failures_found.json',
              'shed2_near.json', 'unclean_cycles.json']:
        d = json.load(open(os.path.join(R, f)))
        if isinstance(d, dict): d = d.get('instances', [])
        for e in d:
            sets, vals = (e['sets'], e['vals']) if isinstance(e, dict) else (e[0], e[1])
            ok, o = no_holds(sets, vals, 1 + max(max(s) for s in sets)); tot += 1; bad += not ok
            if not ok: print('NO-FAIL', f, json.dumps((sets, vals)))
    for t in (2, 3, 4, 5):
        S, V, m = AH.build(t); ok, o = no_holds(S, V, m); print('H%d' % t, len(S), m, 'NO', ok, 'owner', o); tot += 1; bad += not ok
    for t in (3, 4):
        S, V, m = build_hh(t); ok, o = no_holds(S, V, m); print('HH%d' % t, len(S), m, 'NO', ok, 'owner', o); tot += 1; bad += not ok
    print('instances', tot, 'NO failures', bad)
