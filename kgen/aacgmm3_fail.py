"""Where AACGMM's output (kgen/aacgmm3.py) is not an OC1 completion of the picks: does OC1(t >= 0) hold anyway
(kgen/oc3.c brute force), and what do these starts look like?  Same instances as kgen/aacgmm3.py (same seeds).

    python3 kgen/aacgmm3_fail.py SEED N MMIN MMAX"""
import sys, random, collections, json
from lemmaT3 import reachable
from oc3lib import picks, ORD, brute
from aacgmm3 import aacgmm


def instances(seed, N, lo, hi):
    rng = random.Random(seed)
    for t in range(N):
        m = rng.randint(lo, hi); kind = ['general', 'ident', 'zeros'][t % 3]
        if kind == 'general': raw = [[rng.randint(1, 99) for _ in range(m)] for _ in range(3)]
        elif kind == 'ident':
            base = [rng.randint(5, 60) for _ in range(m)]; raw = [[max(1, b * 4 + rng.randint(-6, 6)) for b in base] for _ in range(3)]
        else: raw = [[rng.choice([0, 0, rng.randint(1, 99)]) for _ in range(m)] for _ in range(3)]
        yield kind, raw, [[raw[i][j] * 2 ** (m + 1) + 2 ** j for j in range(m)] for i in range(3)]


if __name__ == '__main__':
    seed, N, lo, hi = map(int, sys.argv[1:5]); C = collections.Counter(); shown = 0
    print('$ python3 kgen/aacgmm3_fail.py', *sys.argv[1:], flush=True)
    for kind, raw, V in instances(seed, N, lo, hi):
        outs = {r: aacgmm(V, r)[0] for r in ORD}; br = brute(V)
        for oi, o in enumerate(ORD):
            y = picks(V, o); own = reachable(V, y, outs[o]); anyr = any(reachable(V, y, X) for X in outs.values())
            oc1 = br[oi]['CODE'] > 0
            C[kind + ': starts'] += 1; C[kind + ': OC1 holds (brute force)'] += oc1
            if not own:
                C[kind + ': AACGMM output (roles = order) not OC1'] += 1; C[kind + ':   ... but OC1 holds'] += oc1
            if not anyr:
                C[kind + ': no role assignment OC1'] += 1; C[kind + ':   ... but OC1 holds'] += 0
                C[kind + ':   no-role starts where OC1 holds'] += oc1
                pickless = sum(1 for g in y if g is None)
                C[kind + ':   no-role starts with a pickless agent'] += pickless > 0
                zero_picks = any(raw[i][y[j]] == 0 for i in range(3) for j in range(3) if y[j] is not None and i != j)
                C[kind + ':   no-role starts where some agent values another pick at 0'] += zero_picks
                if shown < 4:
                    shown += 1; print('NO-ROLE', kind, json.dumps(raw), 'order', o, 'picks', y, 'OC1 witness', br[oi]['wit'], flush=True)
    for k in sorted(C): print(C[k], k)
