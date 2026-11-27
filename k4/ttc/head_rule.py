"""Can the head of the OC1-HD chain be prescribed?  (k4/ttc.md §10.)  For every order pi whose picks have no one-absorber
completion, and every candidate head o, decide whether some chain of OC1-HD's shape (x_0 dangerous at the start,
x_1..x_{t-1} taking exactly their predecessor's pick, the head taking that pick plus junk) with head x_t = o has a
one-absorber completion with absorber o.  Reports, per order (not per distinct picks):
  last   : o = the last agent of pi works;
  some   : some o works;
  every unwanted : every agent whose pick nobody wants works;
  some unwanted  : some unwanted agent works.

    python3 k4/ttc/head_rule.py SRC [N SEED] [nmax=5]"""
import sys, json, random, collections, time
import ttclib as T


def good_heads(E, base):
    D = T.dangerous_set(E, base); heads = set(); memo = {}
    for b2, ds in T.DF.moves(E, base, describe=True, all_desc=True).items():
        for kind, path, H in ds:
            if kind != 'chain' or len(path) < 2 or path[0] not in D:
                continue
            if any(H.get(i) for i in range(1, len(path) - 1)):
                continue
            o = path[-1]
            if o in heads:
                continue
            if (b2, o) not in memo:
                memo[(b2, o)] = T.extends_owner(E, b2, o)
            if memo[(b2, o)]:
                heads.add(o)
    return heads


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/head_rule.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); ex = []
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); cache = {}
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0]); b = T.base_of(E, Y)
            if Y not in cache:
                cache[Y] = None if T.extends_A(E, b, 1) else good_heads(E, b)
            G = cache[Y]
            if G is None:
                continue
            F = T.frozen_set(E, b); U = [i for i in range(n) if i not in F]
            C['hard starts (orders)'] += 1
            C['last'] += pi[-1] in G
            C['some'] += bool(G)
            C['every unwanted'] += set(U) <= G
            C['some unwanted'] += bool(G & set(U))
            if pi[-1] not in G and len(ex) < 4:
                ex.append((name, json.dumps((sets, vals)), 'order', pi, 'picks', Y, 'working heads', sorted(G)))
    for k in sorted(C):
        print(k, C[k])
    for e in ex:
        print('  the last agent is no head:', *e)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
