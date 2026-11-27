"""Is the repairing chain a TTC request path?  (k4/ttc.md §5.)  For every hard start and every request preference,
run YRMH-IGYT with each agent p as the head (priority: p, then the others in reverse order of pi), in mode 'one' (stop
at the first trade) and 'head' (stop at the first trade through the head), and test whether the resulting state has a
one-absorber completion.  Reports, per preference: the hard starts repaired by some head ("realizable"), by the last
agent of pi as head, by some unwanted head (an agent whose pick nobody wants), and by every unwanted head; and how
the repairing heads sit in the order.

    python3 k4/ttc/ttc_heads.py SRC [N SEED] [prefs=val,minval,...] [nmax=5]"""
import sys, random, collections, json, time
import ttclib as T


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a)
    prefs = kw.get('prefs', 'val,minval,minimal,lean,small,val/minval,minval/val').split(',')
    nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/ttc_heads.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); ex = collections.defaultdict(list)
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m)
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
            if T.extends_A(E, b, 1):
                continue
            C['hard starts'] += 1
            F = T.frozen_set(E, b)
            for pref in prefs:
                good = set()
                for p in range(n):
                    prio = [p] + [i for i in pi[::-1] if i != p]
                    for mode in ('one', 'head'):
                        b2, tr = T.yrmh(E, b, prio, pref, 'pi', mode)
                        if tr and T.extends_A(E, b2, 1):
                            good.add(p)
                unw = [p for p in range(n) if p not in F]
                C[pref + ': some head'] += bool(good)
                C[pref + ': last agent of pi'] += pi[-1] in good
                C[pref + ': some unwanted head'] += bool(good & set(unw))
                C[pref + ': every unwanted head'] += set(unw) <= good
                if not good and len(ex[pref]) < 2:
                    ex[pref].append((name, json.dumps((sets, vals)), pi, Y))
    H = C['hard starts']
    print('hard starts', H)
    for pref in prefs:
        print('%-12s some head %d, last agent %d, some unwanted head %d, every unwanted head %d  (of %d)' % (
            pref, C[pref + ': some head'], C[pref + ': last agent of pi'], C[pref + ': some unwanted head'],
            C[pref + ': every unwanted head'], H))
    for pref, l in ex.items():
        for e in l:
            print('no head works for', pref, *e)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
