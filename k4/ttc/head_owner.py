"""Does the pool belong to the chain's head?  (k4/ttc.md §8.)  In Abdulkadiroglu-Sonmez's TTC with an ordering, every
vacant house points to the top-priority agent, so a chain ending at a vacant house executes only when its head is that
agent: the pool is the head's endowment.  Here: for every hard start (picks without a one-absorber completion) and
every improving chain x_0, ..., x_t (de_free moves, chains only; x_t is the head, whose old base becomes junk), test
the one-absorber completion with the absorber prescribed (ttclib.extends_owner):
  head : absorber x_t;   x0 : absorber x_0;   none : no absorber;   off : some agent off the chain;   any : any agent.
Counts the hard starts with some repairing chain of each kind, and, for t = 0 moves (x_0 adds junk), head = x_0.

    python3 k4/ttc/head_owner.py SRC [N SEED] [nmax=5]"""
import sys, json, random, collections, time
import ttclib as T


def main(argv):
    src = argv[0]; rest = argv[1:]
    N = int(rest[0]) if rest and rest[0].isdigit() else 0
    seed = int(rest[1]) if len(rest) > 1 and rest[1].isdigit() else 0
    kw = dict(a.split('=', 1) for a in rest if '=' in a); nmax = int(kw.get('nmax', '5'))
    print('$ python3 k4/ttc/head_owner.py', *argv, flush=True)
    t0 = time.time(); C = collections.Counter(); rng = random.Random(seed + 7); ex = []
    for name, sets, vals, m in T.load_items(src, N, seed):
        n = len(sets)
        if n > nmax:
            continue
        E = T.Enc(sets, vals, m); seen = set()
        for pi in T.orders_of(n, rng):
            Y = tuple(T.sd(E, pi)[0])
            if Y in seen:
                continue
            seen.add(Y); base = T.base_of(E, Y)
            if T.extends_A(E, base, 1):
                continue
            C['distinct hard starts'] += 1
            kinds = collections.Counter(); memo = {}
            def ok(b, o):
                if (b, o) not in memo:
                    memo[(b, o)] = T.extends_owner(E, b, o)
                return memo[(b, o)]
            for b2, ds in T.DF.moves(E, base, describe=True, all_desc=True).items():
                for kind, path, H in ds:
                    if kind != 'chain':
                        continue
                    x0, xt = path[0], path[-1]
                    if ok(b2, xt): kinds['head'] += 1
                    if ok(b2, x0): kinds['x0'] += 1
                    if ok(b2, None): kinds['none'] += 1
                    if any(ok(b2, o) for o in range(n) if o not in path): kinds['off'] += 1
                    if ok(b2, xt) and len(path) > 1: kinds['head, t >= 1'] += 1
            for k in ('head', 'head, t >= 1', 'x0', 'none', 'off'):
                C['some repairing chain with absorber ' + k] += kinds[k] > 0
            if not kinds['head'] and len(ex) < 3:
                ex.append((name, json.dumps((sets, vals)), 'picks', Y))
    for k in sorted(C):
        print(k, C[k])
    for e in ex:
        print('  no repairing chain whose head absorbs:', *e)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
