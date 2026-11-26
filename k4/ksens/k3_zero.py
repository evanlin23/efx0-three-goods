"""Smallest found k = 3 instance whose picks (from some order) do not extend without a chain, while one chain repairs
(k4/ksens.md §8; the bottom rung of the ladder: no chain suffices for k <= 2, K3.SD2).  Random search over n = 2, 3,
m small, every agent valuing at most 3 goods; checked by ocsat and brute force.

    python3 k4/ksens/k3_zero.py SEED T"""
import sys, random, json
import _paths
import ocsat, brute

if __name__ == '__main__':
    seed, T = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed); best = None
    print('$ python3 k4/ksens/k3_zero.py', *sys.argv[1:], flush=True)
    for t in range(T):
        n = rng.choice([2, 3]); m = rng.randint(n + 1, 6)
        sets = [sorted(rng.sample(range(m), rng.randint(2, min(3, m)))) for _ in range(n)]
        if len(set().union(*map(set, sets))) < m: continue
        vals = [rng.sample(range(1, 20), len(s)) for s in sets]
        res = ocsat.report(sets, vals, m)
        bad = [Y for Y, r in res.items() if not r['ext']]
        if bad and (best is None or (n, m) < best[0]):
            b, _ = brute.report(sets, vals, m)
            assert all(not b[Y]['ext'] for Y in bad)
            best = ((n, m), sets, vals, bad[0], res[bad[0]])
            print('n %d m %d' % (n, m), json.dumps((sets, vals)), 'picks', bad[0], 'order', res[bad[0]]['order'],
                  'one chain repairs:', res[bad[0]]['oc'], '(brute force agrees)', flush=True)
    print('smallest:', best[0] if best else None)
