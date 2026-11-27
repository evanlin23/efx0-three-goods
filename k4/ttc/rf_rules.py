"""Which receiver-first order (k4/ttc.md §14.9; coordinator, 06:36): candidate canonical RF-exists rules, tested on
failing (profile, picks) pairs with their SD orders and receivers.

For a failing start Y with an order o giving it and a receiver u:
  - ROT(o):   the rotation (u, o - u) (Conjecture RF's every-order form, refuted at k = 5 by ksens's twins);
  - YRMH(o):  You-Request-My-House-I-Get-Your-Turn (Abdulkadiroglu-Sonmez 1999), read as an SD order: the queue is
              (u, o - u); when the agent at the head takes a good that some agent b still in the queue holds at Y (its
              "house"), b moves to the head of the queue and picks next;
  - SHORT:    among the rotations of the listed orders, one whose outcome changes the fewest agents' picks (first in
              the listed order among ties).
A rule works at a start if its outcome is a maximum matching (as large as Y) and satisfies OC1 under the raw checker
k4/sdc/oc1_mc2_rand.Inst.check (any k).  For ROT and YRMH both 'every listed o' and 'the first listed o' are reported.

    python3 k4/ttc/rf_rules.py export FILE.json.gz [STRIDE]      (the certifier's export format)
    python3 k4/ttc/rf_rules.py rf5                               (ksens's k = 5 twin instance)"""
import sys, os, gzip, json, itertools, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'sdc'))
from oc1_mc2_rand import Inst


def receivers(I, Y):
    return [u for u in range(I.n) if Y[u] is not None and
            all(I.v[i].get(Y[u], 0) <= (I.v[i].get(Y[i], 0) if Y[i] is not None else 0) for i in range(I.n) if i != u)]


def yrmh(I, Y, o, u):
    holder = {Y[i]: i for i in range(I.n) if Y[i] is not None}
    queue = [u] + [a for a in o if a != u]; taken = set(); picks = [None] * I.n; order = []
    while queue:
        a = queue.pop(0); order.append(a)
        av = [g for g in I.R[a] if g not in taken]
        if not av:
            continue
        g = max(av, key=lambda h: I.v[a][h]); picks[a] = g; taken.add(g)
        b = holder.get(g)
        if b is not None and b != a and b in queue:
            queue.remove(b); queue.insert(0, b)
    return tuple(picks), tuple(order)


def good(I, Z, size, cache):
    if Z in cache:
        return cache[Z]
    ok = sum(z is not None for z in Z) >= size and I.check(Z) != 'OC1 fails'
    cache[Z] = ok
    return ok


def test(sets, vals, Y, orders, recs):
    """per start: for each rule, does it work for every receiver, and for some receiver?"""
    I = Inst(sets, vals); size = sum(y is not None for y in Y); cache = {}; R = collections.Counter()
    per = collections.defaultdict(list)
    for u in recs:
        rot = [I.sd([u] + [a for a in o if a != u]) for o in orders]
        ym = [yrmh(I, Y, o, u)[0] for o in orders]
        per['ROT every listed o'].append(all(good(I, Z, size, cache) for Z in rot))
        per['ROT first listed o'].append(good(I, rot[0], size, cache))
        per['ROT some listed o'].append(any(good(I, Z, size, cache) for Z in rot))
        per['YRMH every listed o'].append(all(good(I, Z, size, cache) for Z in ym))
        per['YRMH first listed o'].append(good(I, ym[0], size, cache))
        ch = [sum(1 for i in range(I.n) if Z[i] != Y[i]) for Z in rot]
        per['SHORT'].append(good(I, rot[ch.index(min(ch))], size, cache))
    R['starts'] += 1; R['starts with %d receivers' % len(recs)] += 1
    for rule, oks in per.items():
        R['%s: every receiver' % rule] += all(oks)
        R['%s: some receiver' % rule] += any(oks)
    return R


def job(a):
    return test(*a)


if __name__ == '__main__':
    print('$ python3 k4/ttc/rf_rules.py', *sys.argv[1:], flush=True)
    if sys.argv[1] == 'rf5':
        S = [[0, 1, 2, 5, 6], [1, 2, 4, 5, 6], [3, 4, 5, 6], [3, 4, 5, 6]]
        V = [[3, 35, 33, 43, 39], [20, 26, 16, 43, 32], [8, 2, 7, 4], [8, 2, 7, 4]]
        I = Inst(S, V); Y = (6, 5, 4, 3)
        orders = [list(o) for o in itertools.permutations(range(4)) if I.sd(o) == Y]; recs = receivers(I, Y)
        print('orders', orders, 'receivers', recs, 'Y', I.check(Y))
        for u in recs:
            for o in orders:
                Z = I.sd([u] + [a for a in o if a != u]); W, ordW = yrmh(I, Y, o, u)
                print('  o', o, 'ROT', [u] + [a for a in o if a != u], Z, I.check(Z), '| YRMH', list(ordW), W, I.check(W))
        print(dict(test(S, V, Y, orders, recs)))
        sys.exit()
    if sys.argv[1] == 'jsonl':      # rows with sets, vals, picks (orders and receivers recomputed)
        C = collections.Counter()
        for l in open(sys.argv[2]):
            r = json.loads(l); I = Inst(r['sets'], r['vals']); Y = tuple(r['picks'])
            orders = [list(o) for o in itertools.permutations(range(I.n)) if I.sd(o) == Y]
            R = test(r['sets'], r['vals'], Y, orders, receivers(I, Y)); C.update(R)
            print(r.get('list'), r.get('idx'), 'orders', len(orders), 'receivers', receivers(I, Y),
                  {k: v for k, v in R.items() if 'some receiver' in k})
        for key in sorted(C):
            print(key, C[key])
        sys.exit()
    stride = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    d = json.load(gzip.open(sys.argv[2])); tasks = []; k = 0
    for h in d['hypergraphs']:
        for st in h['starts']:
            k += 1
            if k % stride:
                continue
            tasks.append((h['sets'], st['vals'], tuple(st['picks']), st['orders'], st['receivers']))
    print('starts', len(tasks), flush=True)
    C = collections.Counter()
    with mp.Pool() as pool:
        for R in pool.imap_unordered(job, tasks, chunksize=64):
            C.update(R)
    for key in sorted(C):
        print(key, C[key])
