"""At k = 3: does the max-score rule also work over all improving chains of k4/sdc.md §29 (k3lib.chains: middle agents
may take junk, x0 may take three goods), with the exhaustive one-absorber completion?  And the least-omega rule?
This separates "the rule fails at k = 4" from "the rule needs DE trades".
    python3 k4/k3oc1/k3_general_rule.py LOG [MAX]"""
import sys, os, json, re, ast, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, chains, completion, vals, bundles
C = collections.Counter(); MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
def rscore(rk, base):
    V = vals(rk); B = bundles(base, len(rk)); s = 0
    for i in range(len(rk)):
        sums = sorted(set(sum(V[i][g] for g in S) for r in range(4) for S in itertools.combinations(rk[i], r)))
        s += sums.index(sum(V[i].get(g, 0) for g in B[i]))
    return s
for line in read_lines(sys.argv[1]):
    if not line.startswith('HARD'): continue
    if C['hard'] >= MAX: break
    mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
    rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); V = vals(rk)
    b = base_of(ast.literal_eval(mt.group(4)), m)
    if completion(rk, m, b, 1, V) is not None: continue
    C['hard'] += 1
    ch = list(set(nb for nb, d in chains(rk, m, b, V)))
    ok = {nb: completion(rk, m, nb, 1, V) is not None for nb in ch}
    sc = {nb: rscore(rk, nb) for nb in ch}; best = max(sc.values())
    C['every max-score general chain repairs %s' % all(ok[nb] for nb in ch if sc[nb] == best)] += 1
for k in sorted(C): print(k, C[k])
