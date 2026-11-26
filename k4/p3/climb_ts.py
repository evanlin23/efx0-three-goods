"""Adversarial climb against Conjecture TS2 (k4/p3.md section 4): on random (4, 3) cores, change one agent's strict
balanced type at a time (k4/check4.core_domains), keeping the change when the number of rotations that
k4/p3/ts.py needs with B owners does not drop; restart from a fresh core every --steps steps. Prints every instance
reaching --report rotations or more (4 = failure with up to --R rotations) as JSON.
    python3 k4/p3/climb_ts.py --n=5 --restarts=20 --steps=200 [--B=2] [--R=3] [--report=3] [--seed=1]
"""
import sys, os, random, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from p3lib import *
import ts, check4

def need(I, R, B):
    """score: (rotations needed with B owners, rotations needed with 1 owner); R + 1 = failure"""
    r = ts.run(I, R, sorted({B, 1}), None)
    f = lambda x: R + 1 if x is None else x
    return (f(r[B]), f(r[1]))

if __name__ == '__main__':
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1))); n = int(opt.get('n', 5))
    R, B, rep = int(opt.get('R', 3)), int(opt.get('B', 2)), int(opt.get('report', 3))
    print('$ python3 k4/p3/climb_ts.py ' + ' '.join(sys.argv[1:]), flush=True)
    best_all = (0, 0); t0 = time.time(); evals = 0
    for rs in range(int(opt.get('restarts', 20))):
        rc = None
        while rc is None: rc = random_core43(rng, n)
        m, sets = rc
        doms = check4.core_domains(sets, m, False)
        ty = [rng.randrange(len(D)) for D in doms]
        mk = lambda ty: Inst(sets, [[doms[i][ty[i]][g] for g in sets[i]] for i in range(n)], m, f'climb{rs}')
        cur = need(mk(ty), R, B); evals += 1
        for st in range(int(opt.get('steps', 200))):
            i = rng.randrange(n); old = ty[i]; ty[i] = rng.randrange(len(doms[i]))
            f = need(mk(ty), R, B); evals += 1
            if f >= cur:
                if f > cur and f[0] >= rep: print('REACH', f, json.dumps(mk(ty).as_json()), flush=True)
                cur = f
            else: ty[i] = old
        best_all = max(best_all, cur)
        print(f'restart {rs}: n = {n}, m = {m}, final rotations needed (B = {B}): {cur}; evals {evals}, {time.time()-t0:.0f}s', flush=True)
    print('max rotations needed over all climbs:', best_all)
