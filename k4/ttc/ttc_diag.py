"""Print the hard starts on which one mechanism configuration fails (ttclib.run_mech), with the picks, the frozen and
dangerous agents, the trades the mechanism made, and the repairing improving chains (de_free moves) for comparison.

    python3 k4/ttc/ttc_diag.py SRC [N SEED] pref=minval prio=rev mode=rep [show=5] [nmax=5]"""
import sys, json, random, collections
import ttclib as T


def describe_chain(E, base, b2):
    B = T.bundles(E, base); B2 = T.bundles(E, b2)
    ch = [i for i in range(E.n) if sorted(B[i]) != sorted(B2[i])]
    return {i: (B[i], B2[i]) for i in ch}


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a)
    cfg = (kw.get('pref', 'minval'), kw.get('prio', 'rev'), kw.get('mode', 'rep'))
    show = int(kw.get('show', '5')); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/ttc_diag.py', *argv, flush=True)
    rng = random.Random(seed + 7); shown = 0; C = collections.Counter()
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); done = set()
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0]); base = T.base_of(E, Y)
            if (Y, tuple(pi)) in done or T.extends_A(E, base, 1):
                continue
            done.add((Y, tuple(pi)))
            b, k, ok = T.run_mech(E, base, pi, *cfg)
            C['hard'] += 1; C['ok'] += ok
            if ok or shown >= show:
                continue
            shown += 1
            print('\nFAIL', name, json.dumps((sets, vals)), 'm', m)
            print('  order', pi, 'picks', Y, 'junk', [g for g in range(m) if base[g] < 0])
            print('  frozen', sorted(T.frozen_set(E, base)), 'dangerous', sorted(T.dangerous_set(E, base)))
            tr = []
            T.yrmh(E, base, pi, cfg[0], cfg[1], 'one' if cfg[2] != 'full' else 'full', trace=tr)
            for t, nb in tr:
                print('  mechanism trade', t)
            print('  mechanism end state', T.bundles(E, b), 'after', k, 'trades')
            good = []
            for b2 in set(T.DF.iter_chains(E, base)):
                if T.extends_A(E, b2, 1):
                    good.append(describe_chain(E, base, b2))
            print('  repairing chains (%d):' % len(good))
            for g in good[:6]:
                print('    ', g)
    print('\nhard', C['hard'], 'repaired', C['ok'])


if __name__ == '__main__':
    main(sys.argv[1:])
