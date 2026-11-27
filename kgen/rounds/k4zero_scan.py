"""For every eps-lifted failure in a JSONL file: the zero version (values <= EPS -> 0), its goods valued by nobody, and
OC1 / one round for the same order on (i) the zero version and (ii) the zero version with every worthless good deleted,
by k4/sdc's pipeline and the brute force of verify_k4zero.py (kgen/rounds.md §4.3).
    python3 kgen/rounds/k4zero_scan.py FAILS.jsonl [EPS]"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import verify_k4zero as VZ
EPS = int(sys.argv[2]) if len(sys.argv) > 2 else 5
seen = set()
for line in open(sys.argv[1]):
    x = json.loads(line); V = x['vals']; o = tuple(x['order'])
    Z = [[v if v > EPS else 0 for v in row] for row in V]
    key = json.dumps([Z, o])
    if key in seen: continue
    seen.add(key)
    m = len(Z[0]); dead = [g for g in range(m) if all(r[g] == 0 for r in Z)]
    Zd = [[r[g] for g in range(m) if g not in dead] for r in Z]
    a1 = VZ.sdc_pipeline(Z, o); b1 = VZ.brute(Z, o)
    a2 = VZ.sdc_pipeline(Zd, o); b2 = VZ.brute(Zd, o)
    k = max(sum(1 for v in r if v > 0) for r in Z)
    print(json.dumps(Z), 'order', o, 'k', k, 'worthless goods', dead)
    print('   zero version      : sdc oc1 %s | brute oc1 %s round %s two rounds %s md %s' % (a1['oc1'], b1['oc1'], b1['round_1'], b1.get('two_rounds_1'), b1['md']))
    print('   worthless deleted : sdc oc1 %s | brute oc1 %s round %s md %s' % (a2['oc1'], b2['oc1'], b2['round_1'], b2['md']), flush=True)
