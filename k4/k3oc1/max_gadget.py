"""Non-perfect maximum-matching starts built on purpose: take hard perfect drafts (I0, order) from the logs and add
the gadget s1, s2, s3 (each valuing the cycle g1, g2, g3 of three new goods, a rotation of it as ranking, last in the
order but before u) and a pickless agent u valuing {g1, g2, g3}.  The picks are still a maximum matching (u cannot be
matched), the gadget agents value no junk (Lemma MAX), and by Lemma RED the start behaves like I0 plus a null agent.
Is the draft hard, and does one DE trade / one move repair it?
    python3 k4/k3oc1/max_gadget.py LOG [MAX]"""
import sys, os, json, re, ast, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import sd, base_of, read_lines, chains, completion, vals
from de_moves import de_trades
from lbtest import lb2
from oc1_max import nu, exact
C = collections.Counter(); MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
for line in read_lines(sys.argv[1]):
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    if not mt: continue
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); order = list(ast.literal_eval(mt.group(3)))
    Y0 = ast.literal_eval(mt.group(4))
    if any(g is None for g in Y0) or lb2(rk, m, base_of(Y0, m)): continue    # hard perfect drafts only
    C['hard perfect I0'] += 1
    if C['hard perfect I0'] > MAX: break
    n0 = len(rk); g1, g2, g3 = m, m + 1, m + 2
    rk2 = rk + [(g1, g2, g3), (g2, g3, g1), (g3, g1, g2), (g1, g2, g3)]; m2 = m + 3
    order2 = order + [n0, n0 + 1, n0 + 2, n0 + 3]
    Y = sd(rk2, m2, order2); b = base_of(Y, m2)
    assert Y[n0 + 3] is None and sum(1 for g in Y if g is not None) == nu([list(r) for r in rk2])
    if lb2(rk2, m2, b): C['with the gadget: picks complete'] += 1; continue
    C['with the gadget: HARD'] += 1
    mv = de_trades(rk2, m2, b)
    if any(lb2(rk2, m2, nb) for nb, d in mv): C['  one DE trade repairs'] += 1; continue
    V = vals(rk2); g = any(exact(rk2, m2, nb, V) for nb, d in chains(rk2, m2, b, V))
    C['  no DE trade; one move repairs %s' % g] += 1
    print('NOT REPAIRED BY A DE TRADE', json.dumps([list(r) for r in rk2]), m2, order2, 'one move', g, flush=True)
for k in sorted(C): print(k, C[k])
