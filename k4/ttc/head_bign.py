"""OC1-H beyond n = 5 (k4/ttc.md §8): instances with n = 6..9 (random: oc1_bign's generator via 'big:6-9'; or the
logged instances, 'logs' with nmax=9), a sample of orders (identity, reverse and random), and for every hard start
(picks without a one-absorber completion): does some improving chain with t >= 1 have a one-absorber completion
whose absorber is its head (ttclib.iter_chains_path, lazily, stopping at the first)?  Also records plain OC1 (any
absorber) on the way.  A per-start time limit marks a start 'timeout' (never counted as a pass).

    python3 k4/ttc/head_bign.py SRC [N SEED] [nmin=6] [nmax=9] [orders=12] [tlim=120] [ends=1] [shape=hd]
ends=1: Conjecture OC1-E (the absorber may be x_0 or the head); shape=hd: only chains of OC1-HD's shape count
(OC1-ED with ends=1).  The result 'head' / 'x0' says which endpoint absorbed first.  (Workers are forked, so the
flags set in main reach them.)"""
import sys, os, json, random, collections, time, multiprocessing as mp
import ttclib as T


ENDS = False    # ends=1: OC1-E, the absorber may be x_0 or the head
SHAPE = False   # shape=hd: only chains of OC1-HD's shape (x_0 dangerous, no junk for x_1..x_{t-1})


def check(E, base, tlim):
    t0 = time.time(); seen = set(); oc1 = False
    D = T.dangerous_set(E, base); B = T.bundles(E, base)
    for b2, path in T.iter_chains_path(E, base):
        if len(path) < 2:
            continue
        key = (b2, path)
        if key in seen:
            continue
        seen.add(key)
        if SHAPE:
            B2 = T.bundles(E, b2)
            if path[0] not in D or any(sorted(B2[path[i]]) != sorted(B[path[i - 1]]) for i in range(1, len(path) - 1)):
                if not oc1 and T.extends_A(E, b2, 1):
                    oc1 = True
                continue
        if T.extends_owner(E, b2, path[-1]):
            return 'head', True
        if ENDS and T.extends_owner(E, b2, path[0]):
            return 'x0', True
        if not oc1 and T.extends_A(E, b2, 1):
            oc1 = True
        if time.time() - t0 > tlim:
            return 'timeout', oc1
    return None, oc1


def job(args):
    name, sets, vals, m, nord, seed, tlim = args
    E = T.Enc(sets, vals, m); rng = random.Random(seed); C = collections.Counter(); bad = []; done = {}
    for pi in T.orders_of(len(sets), rng, nord):
        Y = tuple(T.sd(E, pi)[0])
        if Y in done:
            continue
        b = T.base_of(E, Y)
        if T.extends_A(E, b, 1):
            done[Y] = 0; continue
        r, oc1 = check(E, b, tlim); done[Y] = r
        C['distinct hard starts'] += 1; C['head absorbs: %s' % r] += 1; C['OC1 (any absorber) seen'] += oc1
        if r is None:
            bad.append((pi, Y, oc1))
    return name, len(sets), sets, vals, m, C, bad


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a)
    nmin, nmax = int(kw.get('nmin', '6')), int(kw.get('nmax', '9'))
    nord = int(kw.get('orders', '12')); tlim = float(kw.get('tlim', '120'))
    global ENDS, SHAPE
    ENDS = kw.get('ends', '0') == '1'; SHAPE = kw.get('shape', '') == 'hd'
    print('$ python3 k4/ttc/head_bign.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter()
    items = [(nm, s, v, m, nord, seed * 7919 + k, tlim) for k, (nm, s, v, m) in enumerate(T.load_items(src, N, seed))
             if nmin <= len(s) <= nmax]
    with mp.Pool(max(1, (os.cpu_count() or 2) - 1)) as pool:
        for name, n, sets, vals, m, c, bad in pool.imap_unordered(job, items):
            C['instances n=%d' % n] += 1
            for k, v in c.items():
                C['n=%d %s' % (n, k)] += v
            for pi, Y, oc1 in bad:
                print('OC1-H FAILS', name, json.dumps({'sets': sets, 'vals': vals, 'm': m, 'order': pi, 'picks': Y,
                                                       'OC1 chain seen': oc1}), flush=True)
    for k in sorted(C):
        print(k, C[k])
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
