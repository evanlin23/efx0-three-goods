"""Shrink a VM1 counterexample (k4/vm.md section 7.7): repeatedly delete one valued good from one agent's set (that
agent's value for it becomes 0) or one good from the instance, keeping VM1 failing (vm1_fast with 50x caps), and
report the smallest instance reached and its k = max |R_i|.  Then try every way of cutting each agent with |R_i| = 5
down to 4 goods (all combinations), to see whether a 4-limited instance still fails.  EVIDENCE only; failures are
re-checked uncapped by vm1_verify.py / an independent replay.
    python3 k4/vm/vm1_shrink.py JSON"""
import sys, os, json, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import vm1_fast as F

V.FREE_Z[0] = True
CAP = 2000


def compact(sets, vals):
    used = sorted(set(g for S in sets for g in S)); mp_ = {g: k for k, g in enumerate(used)}
    return [[mp_[g] for g in S] for S in sets], [list(v) for v in vals], len(used)


def fails(args):
    sets, vals = args
    sets, vals, m = compact(sets, vals)
    if any(len(S) == 0 for S in sets): return False
    I = V.Inst(sets, vals, m)
    try:
        d = F.vm1(I, 50 * CAP)
    except Exception:
        return False
    return d is None


def cuts(sets, vals):
    for i in range(len(sets)):
        for t in range(len(sets[i])):
            S = [list(s) for s in sets]; W = [list(v) for v in vals]
            del S[i][t]; del W[i][t]; yield S, W


if __name__ == '__main__':
    J = json.loads(sys.argv[1]); sets, vals = J['sets'], J['vals']
    print('$ python3 k4/vm/vm1_shrink.py', sys.argv[1]); assert fails((sets, vals))
    with mp.Pool(os.cpu_count()) as pool:
        changed = True
        while changed:
            changed = False
            cand = list(cuts(sets, vals))
            for (S, W), bad in zip(cand, pool.map(fails, cand)):
                if bad:
                    sets, vals = S, W; changed = True
                    print('  cut -> sizes', [len(s) for s in sets], flush=True); break
        s2, v2, m = compact(sets, vals)
        print('smallest by single cuts: k = %d, n = %d, m = %d %s' % (max(map(len, s2)), len(s2), m,
              json.dumps({'sets': s2, 'vals': v2, 'm': m})))
        # every way of cutting the 5-good agents of the ORIGINAL instance down to 4
        sets, vals = J['sets'], J['vals']
        big = [i for i in range(len(sets)) if len(sets[i]) >= 5]
        opts = [list(itertools.combinations(range(len(sets[i])), len(sets[i]) - 4)) for i in big]
        cand = []
        for choice in itertools.product(*opts):
            S = [list(s) for s in sets]; W = [list(v) for v in vals]
            for i, drop in zip(big, choice):
                S[i] = [g for t, g in enumerate(sets[i]) if t not in drop]; W[i] = [w for t, w in enumerate(vals[i]) if t not in drop]
            cand.append((S, W))
        res = pool.map(fails, cand)
        print('4-limited cuts of the original: %d tried, %d still fail VM1' % (len(cand), sum(res)))
        for (S, W), bad in zip(cand, res):
            if bad:
                s2, v2, m = compact(S, W); print('  FAIL', json.dumps({'sets': s2, 'vals': v2, 'm': m}))
