"""A lexicographic potential for rotations (k4/sdc.md §25).  At an LB4r state s without an output, call a RotStep s -> s'
*lex-improving* if s' has an output, or delta(s') < delta(s) (Lemma K's deficit, best owner and kept set), or
delta(s') = delta(s) and the base values improve in the sense SECOND:
  pareto : every agent's base value weakly up, one strictly;
  sum    : the sum of base values strictly up;
  phi    : the sum of the values of the favourite base goods strictly up.
A *lex-trap* is a reachable state without an output and without a lex-improving rotation.  Mode 'all' explores every
rotation (any reachable state); mode 'guided' (LEX_MODE=guided, one SECOND at a time via LEX_SECOND) follows only
lex-improving rotations from the starts.  No lex-trap in guided mode means every chain of lex-improving rotations from
a start ends at an output: the potential (delta, values) then proves rotation completeness (K4.SDC.RC) on the instance.

    python3 k4/sdc/lex_check.py screen|special|cores:FILES N SEED [DEPTH]"""
import sys, os, json, gzip, random, itertools, collections, time
import _paths
from sdclib import Enc
from sdc_need import instances
from sdc_orders import sd
from blocks4 import M, RM
from nof_var import SPECIAL
from rd_check import state_of

NEG = float('-inf')
GUIDED = os.environ.get('LEX_MODE', 'all') == 'guided'
SECOND = os.environ.get('LEX_SECOND', 'sum')


def basevals(inst, s):
    return tuple(sum(inst.v[i][g] for g in M.base_of(inst, s, i)) for i in range(inst.n))


def phival(inst, s):
    return sum(max([inst.v[i][g] for g in M.base_of(inst, s, i)], default=0) for i in range(inst.n))


if __name__ == '__main__':
    src = sys.argv[1]; C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/sdc/lex_check.py', *sys.argv[1:], flush=True)
    if src == 'special': items = SPECIAL; DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    elif src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); DEPTH = int(sys.argv[4]) if len(sys.argv) > 4 else 3
        rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src); DEPTH = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    for name, sets, vals, m in items:
        n = len(sets)
        if n > 5: continue
        E = Enc(sets, vals, m); v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v); memo = {}
        def info(s):
            if s not in memo:
                memo[s] = (bool(M.any_output(inst, s, 'bundle')), RM.deficit_K(inst, s))
            return memo[s]
        roots = set()
        for o in itertools.permutations(range(n)):
            s0 = state_of(inst, sd(E, list(o))[0])
            for pol in ('shrink', 'envyFree', 'none'):
                roots.add(M.up_run(inst, s0, pol)[0] if pol != 'none' else s0)
        frontier = list(roots); seen = set(roots); traps = collections.Counter()
        for d in range(DEPTH + 1):
            nxt = []
            for s in frontier:
                out, dk = info(s)
                if out: continue
                C['states without output'] += 1
                succ = list(M.rot_steps(inst, s))
                bv, ph = basevals(inst, s), phival(inst, s)
                ok = {'pareto': False, 'sum': False, 'phi': False, 'deficit only': False}
                for s2 in succ:
                    o2, d2 = info(s2)
                    if o2 or d2 < dk:
                        for k in ok: ok[k] = True
                        break
                    if d2 == dk:
                        b2 = basevals(inst, s2)
                        if all(x >= y for x, y in zip(b2, bv)) and b2 != bv: ok['pareto'] = True
                        if sum(b2) > sum(bv): ok['sum'] = True
                        if phival(inst, s2) > ph: ok['phi'] = True
                for k, val in ok.items():
                    if not val: C['lex-trap (%s)' % k] += 1; traps[k] += 1
                if d < DEPTH:
                    for s2 in succ:
                        if GUIDED:
                            o2, d2 = info(s2)
                            b2 = basevals(inst, s2)
                            better = o2 or d2 < dk or (d2 == dk and (
                                (SECOND == 'pareto' and all(x >= y for x, y in zip(b2, bv)) and b2 != bv) or
                                (SECOND == 'sum' and sum(b2) > sum(bv)) or (SECOND == 'phi' and phival(inst, s2) > ph)))
                            if not better: continue
                        if s2 not in seen: seen.add(s2); nxt.append(s2)
            frontier = nxt
        C['instances'] += 1
        for k in traps: C['instances with a lex-trap (%s)' % k] += 1
        if traps.get('sum') and C['shown'] < 4:
            C['shown'] += 1; print('LEX-TRAP (sum)', name, json.dumps((sets, vals)), dict(traps), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
