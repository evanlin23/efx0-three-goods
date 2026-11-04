"""Independent replay of the refutation of NOF-L (k4/sdc.md §15), from the definitions only (no shared code):
neediest-first order with R1 priority (agents that lost a good first; need = top - next two of the available goods;
ties to the smaller index), blocks and their leaders, the last frozen leader l*, and a brute-force search over every
allocation of the unpicked goods for an EFX0 completion of SD(pi) and of SD(pi with l* last).

    python3 k4/sdc/refute_nofl.py"""
import itertools

CASES = {
    'r4253 (n = 4)': ([[0, 2, 5, 6], [1, 4, 6], [2, 3, 4, 5], [3, 4, 5, 6]], [[2, 4, 10, 7], [2, 4, 3], [4, 5, 8, 2], [2, 6, 10, 7]]),
    'r3943 (n = 5)': ([[0, 1, 3, 4], [2, 3, 4, 5], [2, 3, 6], [2, 5, 6], [4, 5, 6]], [[6, 4, 1, 8], [6, 8, 5, 4], [3, 4, 2], [4, 2, 3], [4, 2, 3]]),
}


def run(sets, vals):
    n = len(sets); m = 1 + max(max(s) for s in sets)
    val = [dict(zip(sets[i], vals[i])) for i in range(n)]
    free = set(range(m)); order = []; picks = {}; leaders = []
    while len(order) < n:
        rest = [i for i in range(n) if i not in order]
        lost = [i for i in rest if not set(sets[i]) <= free]
        pool = lost if lost else rest
        def need(i):
            av = sorted((val[i][g] for g in sets[i] if g in free), reverse=True) + [0, 0, 0]
            return av[0] - av[1] - av[2] if any(g in free for g in sets[i]) else -10 ** 9
        i = max(pool, key=lambda a: (need(a), -a))
        if not lost: leaders.append(i)
        av = [g for g in sets[i] if g in free]
        picks[i] = max(av, key=lambda g: (val[i][g], -g)) if av else None
        if picks[i] is not None: free.discard(picks[i])
        order.append(i)
    return n, m, val, order, picks, leaders


def sd(n, sets, val, order):
    free = set(range(1 + max(max(s) for s in sets))); picks = {}
    for i in order:
        av = [g for g in sets[i] if g in free]
        picks[i] = max(av, key=lambda g: (val[i][g], -g)) if av else None
        if picks[i] is not None: free.discard(picks[i])
    return picks


def efx0(n, val, bundles):
    for i in range(n):
        vi = sum(val[i].get(g, 0) for g in bundles[i])
        for j in range(n):
            if i == j: continue
            for h in bundles[j]:
                if sum(val[i].get(g, 0) for g in bundles[j] if g != h) > vi: return False
    return True


def extends(n, m, val, picks):
    rest = [g for g in range(m) if g not in picks.values()]
    for asg in itertools.product(range(n), repeat=len(rest)):
        B = [[picks[i]] if picks[i] is not None else [] for i in range(n)]
        for g, i in zip(rest, asg): B[i].append(g)
        if efx0(n, val, B): return True, B
    return False, None


if __name__ == '__main__':
    print('$ python3 k4/sdc/refute_nofl.py')
    for name, (sets, vals) in CASES.items():
        n, m, val, order, picks, leaders = run(sets, vals)
        frozen = [x for x in leaders if picks[x] is not None and any(j != x and val[j].get(picks[x], 0) > (val[j][picks[j]] if picks[j] is not None else 0) for j in range(n))]
        ls = frozen[-1] if frozen else leaders[-1]
        print(name, 'order', order, 'picks', [picks[i] for i in range(n)], 'leaders', leaders, 'l*', ls)
        print('   plain run extends:', extends(n, m, val, picks)[0])
        p2 = sd(n, sets, val, [i for i in order if i != ls] + [ls])
        print('   l* deferred, picks', [p2[i] for i in range(n)], 'extends:', extends(n, m, val, p2)[0])
        for o in order:
            p3 = sd(n, sets, val, [i for i in order if i != o] + [o]); ok, B = extends(n, m, val, p3)
            print('   defer %d: extends %s %s' % (o, ok, B if ok else ''))
