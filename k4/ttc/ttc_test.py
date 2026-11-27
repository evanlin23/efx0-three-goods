"""Test YRMH-IGYT / TTC-style mechanisms with set demands (ttclib.py) on the starts that need a chain (k4/ttc.md §3).

For every instance and every order pi (all orders for n <= 5; 12 sampled orders, identity and reverse included, for
larger n), take the serial-dictatorship picks Y = SD(pi).  If Y has a one-absorber completion (oc_absorb.extends_A,
A = 1), the start is easy and skipped.  Otherwise, for every configuration (pref, prio, mode) run the mechanism from Y
and record whether the result has a one-absorber completion.  Baseline: the fraction of all improving chains of
de_free.py that repair the start (one-absorber completion after the chain).

    python3 k4/ttc/ttc_test.py SRC [N SEED] [prefs=val,lean,...] [prios=pi,rev,...] [modes=one,full,rep] [nmax=5]
SRC: special | screen | suite | logs | core:n3|n4|n5 | cores:FILES | big:6-9"""
import sys, os, json, random, itertools, collections, time
import ttclib as T

PREFS = ['val', 'lean', 'minimal', 'small', 'minval']
PRIOS = ['pi', 'rev', 'idx', 'danger', 'revdanger']
MODES = ['one', 'full', 'rep']


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a)
    prefs = kw.get('prefs', ','.join(PREFS)).split(',')
    prios = kw.get('prios', ','.join(PRIOS)).split(',')
    modes = kw.get('modes', ','.join(MODES)).split(',')
    nmax = int(kw.get('nmax', '5')); nord = int(kw['orders']) if 'orders' in kw else None
    baseline = kw.get('baseline', '1') == '1'
    print('$ python3 k4/ttc/ttc_test.py', *argv, flush=True)
    t0 = time.time()
    items = T.load_items(src, N, seed)
    C = collections.Counter(); fails = collections.defaultdict(list)
    cfgs = [(p, q, md) for p in prefs for q in prios for md in modes]
    rng = random.Random(seed + 7)
    frac = []
    for name, sets, vals, m in items:
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); C['instances'] += 1
        easy = {}; chains = {}
        for pi in T.orders_of(n, rng, nord):
            Y = tuple(T.sd(E, pi)[0]); base = T.base_of(E, Y)
            if Y not in easy:
                easy[Y] = T.extends_A(E, base, 1)
            C['starts'] += 1
            if easy[Y]:
                continue
            C['hard starts'] += 1
            if baseline and Y not in chains:
                sts = set(T.DF.iter_chains(E, base))
                good = sum(1 for b in sts if T.extends_A(E, b, 1))
                chains[Y] = (good, len(sts))
                C['distinct hard starts'] += 1
                if sts:
                    frac.append(good / len(sts))
            for cfg in cfgs:
                b, k, ok = T.run_mech(E, base, pi, *cfg)
                C[cfg] += ok
                if not ok and len(fails[cfg]) < 3:
                    fails[cfg].append((name, pi))
    print('instances', C['instances'], 'starts', C['starts'], 'hard starts', C['hard starts'],
          'distinct hard starts', C['distinct hard starts'])
    if frac:
        frac.sort()
        print('baseline: fraction of improving chains that repair a distinct hard start: mean %.3f, median %.3f, min %.3f'
              % (sum(frac) / len(frac), frac[len(frac) // 2], frac[0]))
    H = C['hard starts']
    print('%-10s %-10s %-5s %s' % ('pref', 'prio', 'mode', 'repaired / hard starts'))
    for cfg in sorted(cfgs, key=lambda c: -C[c]):
        print('%-10s %-10s %-5s %d / %d%s' % (cfg[0], cfg[1], cfg[2], C[cfg], H, '   ALL' if C[cfg] == H else ''))
    best = max(cfgs, key=lambda c: C[c]) if cfgs else None
    if best and C[best] < H:
        print('first failures of the best configuration', best, fails[best])
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
