"""Is a draft R1-compatible: does its need DAG (i after the holders of the goods it prefers to its pick) have a
linear extension that respects R1 priority (whenever an unprocessed agent has lost one of its goods to a processed
agent, the next agent is such an agent)?  Any linear extension of the need DAG gives the same picks, so an
R1-compatible draft is the Phase 1 output of an LB+ run, and LB+'s Theorems A-C apply to it.
    python3 k4/k3oc1/r1compat.py LOG..."""
import sys, os, json, re, ast, collections
from functools import lru_cache
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines

def r1_compatible(rk, Y):
    n = len(rk)
    holder = {g: i for i, g in enumerate(Y) if g is not None}
    pre = []
    for i in range(n):
        t = rk[i].index(Y[i]) if Y[i] is not None else 3
        pre.append(frozenset(holder[g] for g in rk[i][:t]))
    @lru_cache(maxsize=None)
    def go(done):
        if done == (1 << n) - 1: return True
        taken = set(Y[j] for j in range(n) if done >> j & 1 and Y[j] is not None)
        und = [i for i in range(n) if not done >> i & 1]
        r1 = [i for i in und if any(g in taken for g in rk[i])]
        cand = r1 if r1 else und
        for i in cand:
            if all(done >> j & 1 for j in pre[i]):
                if go(done | (1 << i)): return True
        return False
    return go(0)

if __name__ == '__main__':
    C = collections.Counter()
    for fn in sys.argv[1:]:
        for line in read_lines(fn):
            if not line.startswith('HARD'): continue
            mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
            rk = [tuple(r) for r in json.loads(mt.group(1))]; Y = ast.literal_eval(mt.group(4))
            C['hard'] += 1; C['R1-compatible %s' % r1_compatible(rk, Y)] += 1
    for k in sorted(C): print(k, C[k])
