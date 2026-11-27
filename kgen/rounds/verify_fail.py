"""Confirm a claimed ROUND+ failure by three independent programs, and count the rounds it needs.

    python3 kgen/rounds/verify_fail.py '<vals json>' ORDER...  [--two-brute]

1. rnd.c (rndlib): every EFX allocation, backward round characterization;
2. bruter.py: forward simulation of every round from the definitions, then every completion (raw EFX);
3. k4/ksens/ocsat.py and ocseq.py (SAT; branch claude/k4-ksens at 63089336, path in $KSENS): one round (multi=True),
   free and one absorber; two and three rounds (ocseq multi=True).
Also: the positivity of the values, the SD picks of the order recomputed here, and the raw-definition EFX count.
"""
import sys, os, json, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rndlib, bruter


def main():
    V = json.loads(sys.argv[1]); order = tuple(int(x) for x in sys.argv[2:] if not x.startswith('--'))
    n, m = len(V), len(V[0]); t0 = time.time()
    assert all(x > 0 for row in V for x in row), 'values must be strictly positive'
    Y = bruter.sd(V, order)
    print('instance n %d m %d, order %s, picks %s' % (n, m, order, Y))
    # 1. rnd.c
    res, ne = rndlib.analyze(V)
    s = next(r for r in res if list(r['picks']) == list(Y))
    print('[rnd.c] EFX allocations', ne, 'counts', s['counts'])
    # 2. bruter (forward)
    b = bruter.classify(V, order, two='--two-brute' in sys.argv)
    print('[bruter] ', {k: b[k] for k in b if k != 'picks'}, '%.0fs' % (time.time() - t0), flush=True)
    # 3. SAT
    ks = os.environ.get('KSENS', '/tmp/claude-0/-home-user-efx0-three-goods/1bef8951-d60e-5a6c-a841-d862b0933832/scratchpad/ksens')
    sys.path.insert(0, os.path.join(ks, 'k4', 'ksens')); sys.path.insert(0, os.path.join(ks, 'k4', 'sdc'))
    import ocsat, ocseq
    sets = [list(range(m)) for _ in range(n)]
    O = ocsat.OC(sets, V, m); base = ocsat.bases_of(Y, n)
    r = {'ext_free': O.holds(base, chain='none'), 'ext_1': O.holds(base, chain='none', A=1),
         'oc1': O.holds(base, chain='any', A=1), 'rnd_free': O.holds(base, chain='any', multi=True),
         'rnd_1': O.holds(base, chain='any', A=1, multi=True), 'md': O.holds(base, md=True)}
    O.close()
    print('[ocsat]  ', r, '%.0fs' % (time.time() - t0), flush=True)
    Q = ocseq.Seq(sets, V, m)
    for c in (1, 2, 3):
        f = Q.holds(base, c, None, multi=True); a = Q.holds(base, c, 1, multi=True)
        print('[ocseq]   %d round(s): free %s, one absorber %s' % (c, f, a), '%.0fs' % (time.time() - t0), flush=True)
        if f and a: break
    Q.close()
    agree = (not s['counts']['RND1']) == (not b['rnd_1']) == (not r['rnd_1'])
    print('VERDICT one round fails:', s['counts']['RND1'] == 0 and not b['rnd_1'] and not r['rnd_1'] and not r['rnd_free'],
          '| three implementations agree:', agree)


if __name__ == '__main__':
    main()
