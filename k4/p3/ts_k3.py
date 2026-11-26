"""Cross-check of k4/p3/ts.py at k = 3, where LB+ (Phase 1, upgrades, at most one rotation, one owner) never fails
(proofs/lb_last_step.md, Theorem C): on the certified k = 3 cores with n = 5, 6 (results/certs_5_6.json.gz) under random
rankings (values (4, 3, 2) permuted, a balanced type), ts.py with R = 1 and B = 1 must never fail. Also reports how many
instances need the rotation with one owner and with two owners (B = 2).
    python3 k4/p3/ts_k3.py [--per=20] [--seed=1]        random rankings
    python3 k4/p3/ts_k3.py --all=5                       every ranking profile of the n = 5 cores
"""
import sys, os, random, gzip, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *
import ts

if __name__ == '__main__':
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1))); per = int(opt.get('per', 20))
    print('$ python3 k4/p3/ts_k3.py ' + ' '.join(sys.argv[1:]), flush=True)
    cores = json.load(gzip.open(os.path.join(ROOT, 'results/certs_5_6.json.gz'), 'rt'))
    cnt = collections.Counter(); bad = []
    import itertools
    perms = list(itertools.permutations([4, 3, 2]))
    for c in cores:
        if opt.get('all') and c['n'] != int(opt['all']): continue
        profs = (itertools.product(perms, repeat=c['n']) if opt.get('all')
                 else ([rng.sample([4, 3, 2], 3) for S in c['sets']] for _ in range(per)))
        for vals in profs:
            vals = [list(v) for v in vals]
            I = Inst(c['sets'], vals, c['m'], f"n{c['n']}m{c['m']}")
            r = ts.run(I, 1, [1, 2], None)
            cnt[('B=1', r[1])] += 1; cnt[('B=2', r[2])] += 1
            if r[1] is None: bad.append(I.as_json())
            if r[1] == 1 and r[2] == 0: cnt['rotation replaced by a second owner'] += 1
            if r[1] == 1 and r[2] == 1: cnt['rotation needed with two owners too'] += 1
    for k in sorted(cnt, key=str): print(f'  {k}: {cnt[k]}')
    print('one-owner, one-rotation failures (must be 0 by LB+):', len(bad))
    for b in bad[:3]: print('  ', json.dumps(b))
