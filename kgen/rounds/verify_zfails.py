"""Verify every direct zero-value core failure (fails_zcore.jsonl, kgen/rounds.md §4.5): core test (c4k_core.is_core,
the gm4_counterexample claim), nu, and k4/sdc's own oc1_max_orders.py on all of them; plus OC1' (rnd_oc1z) and the
forward brute force of OC1' (verify_k4zero.oc1_prime) at the failing start.
    python3 kgen/rounds/verify_zfails.py FAILS.jsonl OUT.json"""
import sys, os, json, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, verify_k4zero as VZ, c4k_core
seen = {}; out = []
for l in open(sys.argv[1]):
    x = json.loads(l); V = x['vals']; k = json.dumps(V)
    if k in seen: continue
    m = len(V[0]); d = [{g: r[g] for g in range(m) if r[g] > 0} for r in V]
    core, _ = c4k_core.is_core(d); nu = c4k_core.nu(d)
    res, _ = rndlib.oc1z(V)
    fails = [r for r in res if r['perfect'] and r['OC1'] == 0]
    p_c = all(r['OC1P'] > 0 for r in fails); p_f = all(VZ.oc1_prime(V, r['order']) for r in fails)
    seen[k] = len(out)
    out.append({'sets': [sorted(dd) for dd in d], 'vals': [[dd[g] for g in sorted(dd)] for dd in d]})
    print('instance %d: n %d m %d core %s nu %d | rnd.c: OC1 fails from %d perfect starts %s | OC1\' holds there: rnd.c %s, forward %s'
          % (len(out) - 1, len(V), m, core, nu, len(fails), [list(r['order']) for r in fails][:3], p_c, p_f), flush=True)
json.dump(out, open(sys.argv[2], 'w'))
print(subprocess.run(['python3', 'oc1_max_orders.py', os.path.abspath(sys.argv[2])], cwd=os.path.join(HERE, '..', '..', 'k4', 'sdc'),
                     capture_output=True, text=True).stdout)
