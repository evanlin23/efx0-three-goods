"""For eps-lifted failures (values <= EPS are 'tiny'): the zero version (tiny -> 0, a k-limited EFX0 instance) checked
with k4/ksens/ocsat.py (SAT, any values): does one round (multi=True), free / one absorber, repair the same order?
Also: one chain (OC1), and whether the eps version's failure is confirmed by ocsat itself.
    python3 kgen/rounds/zero_version.py FAILS.jsonl [EPS]"""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
KS = os.environ.get('KSENS', '/tmp/claude-0/-home-user-efx0-three-goods/1bef8951-d60e-5a6c-a841-d862b0933832/scratchpad/ksens')
sys.path.insert(0, os.path.join(KS, 'k4', 'ksens')); sys.path.insert(0, os.path.join(KS, 'k4', 'sdc'))
import ocsat
EPS = int(sys.argv[2]) if len(sys.argv) > 2 else 5
seen = set()
for line in open(sys.argv[1]):
    x = json.loads(line); V = x['vals']; o = tuple(x['order'])
    key = json.dumps([V, o])
    if key in seen: continue
    seen.add(key)
    n, m = len(V), len(V[0])
    out = {}
    for tag, W in (('eps', V), ('zero', [[v if v > EPS else 0 for v in row] for row in V])):
        sets = [[g for g in range(m) if W[i][g] > 0] for i in range(n)]
        vals = [[W[i][g] for g in sets[i]] for i in range(n)]
        Y = ocsat.sd(sets, vals, o, m); b = ocsat.bases_of(Y, n)
        O = ocsat.OC(sets, vals, m)
        out[tag] = {'k': max(map(len, sets)), 'picks': Y, 'round_A1': O.holds(b, chain='any', A=1, multi=True),
                    'round_free': O.holds(b, chain='any', multi=True), 'oc1': O.holds(b, chain='any', A=1),
                    'md': O.holds(b, md=True)}
        O.close()
    print(json.dumps(V), 'order', o, '\n   eps :', out['eps'], '\n   zero:', out['zero'], flush=True)
