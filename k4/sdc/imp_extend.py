"""A value-monotone repair (k4/sdc.md §29).  From the serial-dictatorship start of an order (picks as one-good bases),
after each upgrade policy, search (BFS, reachable set capped) over LB4r RotSteps that are improving for the rotated
agent (v_k(O) > v_k(Y_k)); every reached state dominates the picks in value.  Terminal test: the bases extend to a
complete EFX0 allocation (every base good stays with its holder, the junk anywhere; SAT on sdclib's encoding), which
replaces LB4r's one-owner Output.  Question: from every order, is such a state reachable?

    python3 k4/sdc/imp_extend.py screen|suite|special|logs|cores:FILES N SEED [order:nf]"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import sd
from blocks4 import M
from nof_var import SPECIAL
from rd_check import state_of
from pysat.solvers import Cadical153


def extends(E, s):
    cl = list(E.cl)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if s[0][g] >= 0: cl.append([E.x[g][s[0][g]]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


def search(E, inst, s1, memo, cap=2000):
    def ext(s):
        key = s[0]
        if key not in memo: memo[key] = extends(E, s)
        return memo[key]
    frontier = [s1]; seen = {s1}; d = 0
    while frontier:
        for s in frontier:
            if ext(s): return d
        nxt = []
        for s in frontier:
            for s2, (c, O) in M.rot_steps(inst, s).items():
                k = c[0]
                if not sum(inst.v[k][g] for g in O) > inst.v[k][s[1][k]]: continue
                if s2 not in seen:
                    seen.add(s2); nxt.append(s2)
                    if len(seen) > cap: return 'cap'
        frontier = nxt; d += 1
    return None


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    NF = 'order:nf' in sys.argv
    args = [a for a in sys.argv[1:] if a != 'order:nf']
    print('$ python3 k4/sdc/imp_extend.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL
    elif src.startswith('cores:'):
        N, seed = int(args[1]), int(args[2]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    elif src == 'logs':
        from mdom import __file__ as _mf
        import re, glob
        seen = set(); items = []
        for f in sorted(glob.glob(os.path.join(_paths.ROOT, 'results', 'k4_sdc', '*.log'))):
            for line in open(f, errors='ignore'):
                for mt in re.finditer(r'(\[\[\[[0-9, \[\]]+\]\], \[\[[0-9, \[\]]+\]\]\])', line):
                    try: sets, vals = json.loads(mt.group(1))
                    except Exception: continue
                    if not all(len(a) == len(b) for a, b in zip(sets, vals)) or max(len(a) for a in sets) > 4: continue
                    key = json.dumps((sets, vals))
                    if key in seen: continue
                    seen.add(key); items.append(('log%d' % len(items), sets, vals, 1 + max(max(a) for a in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        n = len(sets)
        if n > (9 if NF else 5): continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v); memo = {}
        C['instances'] += 1
        if NF: orders = [tuple(rule_order(E, 'need2', False)[1])]
        else: orders = list(itertools.permutations(range(n)))
        seenY = {}
        for o in orders:
            Y = tuple(sd(E, list(o))[0]) if not NF else tuple(rule_order(E, 'need2', False)[0])
            if Y in seenY: C['starts'] += 1; C['start result %s' % seenY[Y]] += 1; continue
            best = None
            for pol in ('none', 'envyFree', 'shrink'):
                s0 = state_of(inst, list(Y))
                s1 = M.up_run(inst, s0, pol)[0] if pol != 'none' else s0
                d = search(E, inst, s1, memo)
                if isinstance(d, int) and (best is None or d < best): best = d
                if best == 0: break
            seenY[Y] = best
            C['starts'] += 1; C['start result %s' % best] += 1
            if best is None and C['shown'] < 4:
                C['shown'] += 1; print('NO MONOTONE REPAIR', name, json.dumps((sets, vals)), 'order', o, 'Y', Y, flush=True)
        C['instances with a start without monotone repair'] += any(x is None for x in seenY.values())
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
