"""Random k = 4 cores (EVIDENCE only, PROMPT.md §5 rule 3): hypergraphs that k4/check4.py's is_core accepts
(connected, agent degrees in {3, 4}, every good relevant to someone, at most d - 2 private goods for an agent of
degree d), drawn by rejection: m uniform in [4, 3n], each agent a uniform random set of its degree. Isomorphic copies
are not removed. Written as a core list that k4/lb4_run.py reads.
With --extend=FILE --add=A: each core is a random core of FILE (a core list) with A agents added, each a random set of
3 or 4 goods among the old goods and up to 4 new ones (n is then ignored).
Usage: lb4_randcores.py n COUNT OUT.json.gz [--n4=K] [--seed=S] [--extend=FILE --add=A]
       K = the number of 4-good agents (default: random)"""
import gzip, json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check4

def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--'))
    n, count, out = int(args[0]), int(args[1]), args[2]
    rng = random.Random(int(opt.get('seed', 1)))
    cores = []
    base = json.load(gzip.open(opt['extend'], 'rt'))['cores'] if 'extend' in opt else None
    while base is not None and len(cores) < count:
        c = rng.choice(base); A = int(opt.get('add', 1))
        for _ in range(2000):
            m = c['m'] + rng.randrange(5)
            sets = [list(S) for S in c['sets']] + [sorted(rng.sample(range(m), rng.choice((3, 4)))) for _ in range(A)]
            rng.shuffle(sets)
            if check4.is_core(len(sets), m, sets, False)[0]:
                cores.append({'m': m, 'sets': sets}); break
    while base is None and len(cores) < count:
        n4 = int(opt['n4']) if 'n4' in opt else rng.randrange(n + 1)
        m = rng.randrange(4, 3 * n + 1)
        for _ in range(2000):
            sets = [sorted(rng.sample(range(m), 4 if i < n4 else 3)) for i in range(n)]
            rng.shuffle(sets)                   # the 4-good agents anywhere in the index order
            if check4.is_core(n, m, sets, n4 == n)[0]:
                cores.append({'m': m, 'sets': sets}); break
    cores.sort(key=lambda c: (c['m'], c['sets']))
    with gzip.open(out, 'wt') as fh:
        json.dump({'n': n, 'n4': opt.get('n4', 'random'), 'extend': opt.get('extend'), 'add': opt.get('add'), 'seed': int(opt.get('seed', 1)), 'random': True, 'ties': False,
                   'cores': cores}, fh)
    ns = sorted({len(c['sets']) for c in cores})
    print(f"{out}: {len(cores)} random cores, n = {ns[0]}{'' if len(ns) == 1 else f' to {ns[-1]}'}, "
          f"4-good agents {opt.get('n4', 'random')}, "
          f"m from {cores[0]['m']} to {cores[-1]['m']}")

if __name__ == '__main__':
    main()
