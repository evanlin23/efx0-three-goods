"""Conjecture NOF-L (nofl.py) on the DE4 refutation instances and on H_t, HH_t (the files of nof_files.py).

    python3 k4/sdc/nofl_files.py"""
import os, sys, json, collections
import _paths
from nofl import nofl
sys.path.insert(0, os.path.join(_paths.ROOT, 'k4'))
import adaptive_H as AH
from sdc_ht import build_hh

if __name__ == '__main__':
    print('$ python3 k4/sdc/nofl_files.py')
    R = os.path.join(_paths.ROOT, 'results', 'k4_de4'); C = collections.Counter()
    for f in ['robust_failures.json', 'refute_lp_instance.json', 'refute_rob_instance.json', 'shed_failures_found.json',
              'shed2_near.json', 'unclean_cycles.json']:
        d = json.load(open(os.path.join(R, f)))
        if isinstance(d, dict): d = d.get('instances', [])
        for e in d:
            sets, vals = (e['sets'], e['vals']) if isinstance(e, dict) else (e[0], e[1])
            r, pi, l = nofl(sets, vals, 1 + max(max(s) for s in sets)); C['instances'] += 1; C['result %s' % r] += 1
            if r is None: print('NOF-L FAILS', f, json.dumps((sets, vals)))
    for t in (2, 3, 4, 5):
        S, V, m = AH.build(t); r, pi, l = nofl(S, V, m); print('H%d' % t, len(S), m, 'NOF-L result', r); C['instances'] += 1; C['result %s' % r] += 1
    for t in (3, 4):
        S, V, m = build_hh(t); r, pi, l = nofl(S, V, m); print('HH%d' % t, len(S), m, 'NOF-L result', r); C['instances'] += 1; C['result %s' % r] += 1
    for k in sorted(C): print(k, C[k])
