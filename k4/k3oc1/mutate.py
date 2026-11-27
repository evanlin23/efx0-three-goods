"""Counterexample search for OT near the hardest known drafts: start from the n = 6 drafts where max score needs the
exact test (oc1_fast_small6_partial.maxfail.gz), and repeatedly mutate (re-rank an agent, move one of its goods to
another good, add an agent with three goods at a random position of the order, add a dead good); keep a mutant if its
draft is hard.  Every hard mutant is tested for both rules (OT-omega with the simple test, OT-score with the exact
test) and for one DE trade.
    python3 k4/k3oc1/mutate.py STEPS SEED [NMAX]"""
import sys, os, json, re, ast, random, collections, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE)); sys.path.insert(0, HERE)
from k3lib import sd, base_of, read_lines
from de_moves import de_trades
from lbtest import lb_simple, lb2, parts
from rules import score
steps, seed = int(sys.argv[1]), int(sys.argv[2]); NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 8
rng = random.Random(seed); C = collections.Counter(); t0 = time.time()
seeds = []
for line in read_lines(os.path.join(ROOT, 'results', 'k4_k3oc1', 'oc1_fast_small6_partial.maxfail.gz')):
    mt = re.search(r'MAXFAIL (\[.*?\]\]) (\d+) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(3))
    # recover an order: any linear extension of the need order
    n = len(rk); holder = {g: i for i, g in enumerate(Y) if g is not None}
    pre = [set(holder[g] for g in rk[i][:(rk[i].index(Y[i]) if Y[i] is not None else 3)]) for i in range(n)]
    order = []; left = set(range(n))
    while left:
        i = min(j for j in left if pre[j] <= set(order)); order.append(i); left.discard(i)
    seeds.append((rk, m, order))
def test(rk, m, order):
    b = base_of(sd(rk, m, order), m)
    if lb_simple(rk, m, b): return None
    mv = de_trades(rk, m, b)
    if not mv: return 'NO TRADE'
    simp = [bool(lb_simple(rk, m, nb)) for nb, d in mv]
    ex = [simp[i] or bool(lb2(rk, m, nb)) for i, (nb, d) in enumerate(mv)]
    if not any(ex): return 'NO DE TRADE REPAIRS'
    sc = [score(rk, nb) for nb, d in mv]; om = [(lambda P: len(P[1]) - len(P[5]))(parts(rk, m, nb)) for nb, d in mv]
    res = []
    so = [i for i, k in enumerate(om) if k == min(om)]; ss = [i for i, k in enumerate(sc) if k == max(sc)]
    if not all(simp[i] for i in so): res.append('every least-omega: simple fails')
    if not all(ex[i] for i in so): res.append('every least-omega: exact fails')
    if not any(ex[i] for i in so): res.append('some least-omega: exact fails')
    if not all(ex[i] for i in ss): res.append('every max-score: exact fails')
    if not any(ex[i] for i in ss): res.append('some max-score: exact fails')
    if not any(simp): res.append('some trade: simple fails')
    return ', '.join(res) if res else 'ok'
cur = rng.choice(seeds)
for it in range(steps):
    rk, m, order = cur; rk = [list(r) for r in rk]; order = list(order); n = len(rk)
    op = rng.random()
    if op < 0.35:
        i = rng.randrange(n); rng.shuffle(rk[i])
    elif op < 0.7:
        i = rng.randrange(n); t = rng.randrange(3); g = rng.randrange(m)
        if g not in rk[i]: rk[i][t] = g
    elif op < 0.9 and n < NMAX:
        rk.append(rng.sample(range(m), 3)); order.insert(rng.randrange(n + 1), n)
    else:
        m += 1
    rk = [tuple(r) for r in rk]
    r = test(rk, m, order); C['tests'] += 1
    if r is None:
        if rng.random() < 0.05: cur = rng.choice(seeds)
        continue
    C['hard mutants'] += 1
    for part in r.split(', '): C[part] += 1
    if r != 'ok': print('FOUND', r, json.dumps([list(x) for x in rk]), m, order, flush=True)
    cur = (rk, m, order)
for k in sorted(C): print(k, C[k])
print('time %.0f s' % (time.time() - t0))
