"""Where 'no rotation, two sinks' fails (k4/p3/ts.py with R = 0, B = 2), how many free (non-frozen) agents does the
Phase 1 state have, under each upgrade policy? A second owner needs a second free agent.
    python3 k4/p3/ts_free.py SRC [options of k4/p3/dump_rules.py]
"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *
import ts, dump_rules

if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1)))
    print('$ python3 k4/p3/ts_free.py ' + ' '.join(sys.argv[1:]), flush=True)
    L = dump_rules.load(src, opt, rng)
    cnt = collections.Counter()
    for I in L:
        C = Complete(I); bb = {2: C.big_bound(2), 1: C.big_bound(1)}
        s0, order = ts.initial(I)
        ok = {}
        for pol in (1, 2, 0):
            s = ts.upgrade(s0, pol)
            nfree = sum(not f for f in s.frozen())
            for B in (1, 2):
                ok[(pol, B)] = ts.extends(I, C, s, B, bb) is not None
            cnt[f'policy {pol}: free agents {nfree}: ' + ('B1 ok' if ok[(pol, 1)] else 'B2 ok' if ok[(pol, 2)] else 'fail')] += 1
        any2 = any(ok[(p, 2)] for p in (0, 1, 2)); any1 = any(ok[(p, 1)] for p in (0, 1, 2))
        cnt['instances: some policy B1' if any1 else 'instances: some policy B2 only' if any2 else 'instances: no policy'] += 1
    for k, v in sorted(cnt.items()): print(f'  {k}: {v}')
