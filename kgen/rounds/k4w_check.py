"""Instance K4W (kgen/rounds.md §4.3): a k = 4 instance with zeros and NO worthless good where OC1 and one round fail
at a perfect start.  Every order: picks, perfect or not, and OC1 / one round by three programs (k4/sdc pipeline,
brute force of verify_k4zero.py, ksens ocsat).
    python3 kgen/rounds/k4w_check.py"""
import sys, os, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import verify_k4zero as VZ
KS = os.environ.get('KSENS', '/tmp/claude-0/-home-user-efx0-three-goods/1bef8951-d60e-5a6c-a841-d862b0933832/scratchpad/ksens')
sys.path.insert(0, os.path.join(KS, 'k4', 'ksens'))
import ocsat
K4W = [[0, 2613, 0, 0, 1453, 1599, 1597], [0, 2615, 0, 0, 1474, 1599, 1596],
       [1929, 984, 22, 0, 0, 543, 0], [2334, 0, 2265, 49, 0, 897, 0]]
V = json.loads(sys.argv[1]) if len(sys.argv) > 1 else K4W
n, m = len(V), len(V[0])
sets = [[g for g in range(m) if V[i][g] > 0] for i in range(n)]
vals = [[V[i][g] for g in sets[i]] for i in range(n)]
print('instance', json.dumps(V), 'k', max(map(len, sets)), 'worthless goods', [g for g in range(m) if all(r[g] == 0 for r in V)])
for i in range(n):
    s = sorted(vals[i], reverse=True); print('  agent %d: relevant %s, top %d vs rest %d (%s)' % (i, sets[i], s[0], sum(s[1:]), 'top-heavy' if s[0] >= sum(s[1:]) else 'balanced'))
O = ocsat.OC(sets, vals, m); seen = {}
for o in itertools.permutations(range(n)):
    Y = tuple(ocsat.sd(sets, vals, o, m))
    if Y in seen: continue
    seen[Y] = o
    b = ocsat.bases_of(Y, n)
    sat = {'oc1': O.holds(b, chain='any', A=1), 'round_1': O.holds(b, chain='any', A=1, multi=True), 'round_free': O.holds(b, chain='any', multi=True)}
    a = VZ.sdc_pipeline(V, o); br = VZ.brute(V, o)
    perfect = all(y is not None for y in Y)
    agree = (sat['oc1'] == a['oc1'] == br['oc1']) and (sat['round_1'] == br['round_1'])
    print('order %s picks %s perfect %s | ocsat %s | sdc oc1 %s | brute oc1 %s round %s two rounds %s md %s | agree %s'
          % (o, list(Y), perfect, sat, a['oc1'], br['oc1'], br['round_1'], br.get('two_rounds_1'), br['md'], agree), flush=True)
O.close()
