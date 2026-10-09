"""LS: serial dictatorship, then Pareto-improving moves until none applies, then slot filling and one absorber.
Branch proof/k3-simplify, exploration "matching". A CANDIDATE; evidence only. Core case: every agent has three goods
a > b > c, strictly balanced (values 4, 3, 2); goods nobody ranks are worthless.

  1. Start: serial dictatorship in index order (every agent takes its favourite remaining good, or nothing).
  2. Moves, while one applies (each makes every agent it touches strictly better, keeps the state valid; the sum of
     utilities nothing < c < b < a < {b, c} grows, so this stops):
       up     an agent holding b, with c left over and b needed by nobody, takes c too        (K3S step 2)
       cycle  agents holding one good each trade around a cycle, each getting a good it needs
       rot    an agent x holding a_x takes {b_x, c_x} instead; a_x goes along a need chain (j_1 needs a_x, j_2
              needs j_1's good, ...), the last agent's good is released; b_x, c_x must be left over or the released
              good, and the result must be valid (nobody needs a good that ends up left over)
  3. Completion: if the leftovers fit the slots (2 per agent holding nothing, 1 per agent holding one good nobody
     needs), fill them. Otherwise an absorber o (rule below) takes what the other slots cannot take, after one good of
     each pair exposed for o has been put into another slot.

  python3 ls.py small N M | cores MAXN SAMPLE MINN | random K SEED MAXN [absorber rule]
"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
from common import Base, held, efx0_rank
from exp_local import one_moves

def sd(rank, m):
    used = set(); opt = []
    for r in rank:
        t = next((t for t, g in enumerate(r) if g not in used), None)
        if t is None: opt.append(0)
        else: opt.append(t + 1); used.add(r[t])
    return tuple(opt)

PREF = {'up': 0, 'cycle': 1, 'rot': 2}

def local_search(rank, m, opt, info=None, kinds=('up', 'cycle', 'rot')):
    steps = collections.Counter()
    while True:
        mv = [x for x in one_moves(rank, m, opt) if x[0] in kinds]
        if not mv: break
        mv.sort(key=lambda x: PREF[x[0]])
        kind, who, o2 = mv[0]
        steps[kind] += 1; opt = o2
    if info is not None: info['steps'] = steps
    return opt

def absorber_candidates(b):
    return [i for i in range(b.n) if i in b.free or b.opt[i] == 4]

def deficit(b, o):
    """|minimum hitting set of the pairs exposed for o| - slots of the other free agents; inf if a pair lies in o's base"""
    from common import min_hitting
    pairs = b.hit_pairs(o)
    if pairs is None: return float('inf')
    H = min_hitting(pairs, 99)
    return len(H) - sum(b.slots[f] for f in b.free if f != o)

RULES = {
    'any': lambda b, c: c,
    'mindef': lambda b, c: [min(c, key=lambda o: (deficit(b, o), o))],
    'minexp': lambda b, c: [min(c, key=lambda o: (len(b.exposed(o)), o))],
    'empty_then_minexp': lambda b, c: [next((o for o in c if b.opt[o] == 0), None) or min(c, key=lambda o: (len(b.exposed(o)), o))],
    'last': lambda b, c: [c[-1]],
    'first': lambda b, c: [c[0]],
}

def ls(rank, m, rule='mindef', info=None, start=None, kinds=('up', 'cycle', 'rot')):
    opt = local_search(rank, m, start or sd(rank, m), info, kinds)
    b = Base(rank, m, opt)
    assert b.valid
    c = absorber_candidates(b)
    if not c: return None
    for o in RULES[rule](b, c):
        X = b.complete(o)
        if X is not None:
            if info is not None: info['absorber'] = o; info['overflow'] = b.overflow(); info['opt'] = opt
            return X
    if info is not None: info['opt'] = opt; info['overflow'] = b.overflow()
    return None

if __name__ == '__main__':
    from test_k3s import gen_small
    from lbx import core_profiles
    mode = sys.argv[1]
    rule = 'mindef'
    kinds = ('up', 'cycle', 'rot')
    args = sys.argv[2:]
    if args and args[-1].startswith('kinds='): kinds = tuple(args.pop()[6:].split(','))
    if args and args[-1] in RULES: rule = args.pop()
    if mode == 'small':
        n, m = int(args[0]), int(args[1]); src = ((r, m) for _, _, r in gen_small(n, m)); title = f"small n={n} m={m}"
    elif mode == 'cores':
        N, S, lo = int(args[0]), int(args[1]), int(args[2])
        src = ((r, m) for _, m, r in core_profiles(N, sample=S, minn=lo)); title = f"cores n in [{lo},{N}] sample={S}"
    else:
        K, seed, N = int(args[0]), int(args[1]), int(args[2]); rng = random.Random(seed)
        def gen():
            for _ in range(K):
                n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 3)
                yield [tuple(rng.sample(range(m), 3)) for _ in range(n)], m
        src = gen(); title = f"random K={K} seed={seed} 2<=n<={N} n<=m<=2n+3"
    tot = 0; bad = []; steps = collections.Counter(); moved = collections.Counter(); ab = collections.Counter()
    for rank, m in src:
        tot += 1; info = {}
        X = ls(rank, m, rule, info, kinds=kinds)
        steps.update(info['steps']); moved[sum(info['steps'].values())] += 1
        ab['overflow>0' if info.get('overflow', 0) > 0 else 'fits'] += 1
        if not efx0_rank(rank, m, X):
            bad.append((len(rank), m, rank, info.get('opt')))
    bad.sort(key=lambda t: (t[0], t[1]))
    print(f"LS rule={rule} kinds={','.join(kinds)} {title}: {tot} profiles; not EFX0: {len(bad)}; moves {dict(steps)}; "
          f"#moves per profile {dict(sorted(moved.items()))}; {dict(ab)}")
    for x in bad[:3]: print("  fail:", x)
