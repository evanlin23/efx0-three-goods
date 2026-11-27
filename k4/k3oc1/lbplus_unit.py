"""LB+ with slots of size one on R1-compatible drafts (k4/k3_oc1.md, Theorem R1C).  For a hard draft whose need DAG has
an R1-priority linear extension pi*: LB's maximal upgrades; r = the last agent of pi* not upgraded; owner r by
Lemma 1 with unit caps; otherwise the bad case: k* = the leader (fresh agent) of the last block of pi*, rotate along
every need chain from k* to r (Theorem B) and test the exact one-absorber completion (lbtest.lb2) afterwards.
Checks that the run never fails, i.e. that proofs/lb_last_step.md goes through with unit caps.
    python3 k4/k3oc1/lbplus_unit.py LOG..."""
import sys, os, json, re, ast, collections
from functools import lru_cache
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from k3lib import base_of, read_lines, bundles
from lbtest import upgrade, parts, exposed, min_hit, lb2

def r1_extension(rk, Y):
    n = len(rk); holder = {g: i for i, g in enumerate(Y) if g is not None}
    pre = [frozenset(holder[g] for g in rk[i][:(rk[i].index(Y[i]) if Y[i] is not None else 3)]) for i in range(n)]
    @lru_cache(maxsize=None)
    def go(done):
        if done == (1 << n) - 1: return ()
        taken = set(Y[j] for j in range(n) if done >> j & 1 and Y[j] is not None)
        und = [i for i in range(n) if not done >> i & 1]
        r1 = [i for i in und if any(g in taken for g in rk[i])]
        for i in (r1 if r1 else und):
            if all(done >> j & 1 for j in pre[i]):
                rest = go(done | (1 << i))
                if rest is not None: return (i,) + rest
        return None
    return go(0)

def run(rk, m, Y):
    n = len(rk); order = r1_extension(rk, Y)
    if order is None: return 'not R1-compatible'
    b = upgrade(rk, m, base_of(Y, m)); B, J, U, NA, F, T = parts(rk, m, b)
    if len(J) <= len(T): return 'no owner'
    r = [i for i in order if not U[i]][-1]
    E = exposed(rk, b, r, B, J, U)
    if min_hit([[g for g in (rk[x][1], rk[x][2]) if g in J] for x in E], len(T) - 1) is not None: return 'owner r'
    # blocks of pi*: a fresh agent (all its goods still free) starts a block
    taken = set(); leader = None
    for i in order:
        if all(g not in taken for g in rk[i]): leader = i
        if Y[i] is not None: taken.add(Y[i])
    k = leader
    if k == r or B[k] != [rk[k][0]] or k not in E or k in T: return 'BAD CASE VIOLATED'
    # need chains from k to r (followers: agents not upgraded that need the current agent's good)
    res = []
    def walk(path):
        j = path[-1]
        if j == r: res.append(list(path)); return
        g = B[j][0]
        for w in range(n):
            if w in path or U[w] or not B[w] and False: continue
            if U[w]: continue
            if g in rk[w] and (not B[w] or rk[w].index(g) < rk[w].index(B[w][0])): walk(path + [w])
    walk([k])
    if not res: return 'NO NEED CHAIN TO r'
    out = []
    for path in res:
        nb = list(b)
        for g in B[r]: nb[g] = -1
        for t in range(len(path) - 1, 0, -1): nb[B[path[t - 1]][0]] = path[t]
        nb[rk[k][1]] = k; nb[rk[k][2]] = k
        out.append(bool(lb2(rk, m, tuple(nb))))
    return 'rotation: all chains complete %s' % all(out)

if __name__ == '__main__':
    C = collections.Counter()
    for fn in sys.argv[1:]:
        for line in read_lines(fn):
            if not line.startswith('HARD'): continue
            mt = re.match(r'HARD (\[.*?\]\]) (\d+) order (\(.*?\)) picks (\(.*?\))', line)
            rk = [tuple(r) for r in json.loads(mt.group(1))]; m = int(mt.group(2)); Y = ast.literal_eval(mt.group(4))
            C[run(rk, m, Y)] += 1
    for k in sorted(C): print(k, C[k])
