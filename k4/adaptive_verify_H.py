"""Proposition H' of k4/adaptive.md §3, checked with the independent LB4r model of PR #33 (k4/c4_verify_H/lb4r.py and
hcore.py, written from lean/EFX/LB4R.lean by a verifier; no code shared with k4/adaptive.c).

Claim: on H_t, if some agent of gadget 1 is inserted before l, then in Phase 1 no y_j takes e_j (no cascade), after
need-shrinking upgrades no agent has a need (NA is empty), and the owner r (the last-processed agent that is not
upgraded) has an output: LB4r succeeds with no rotation, whatever the rest of the insertion sequence. Contrast: if l is
inserted while gadget 1 is untouched, y_1 takes e_1.
For each t, random insertion sequences (tau as in LB4R.lean: the j-th insertion step takes the (tau_j mod u)-th
unprocessed agent in index order) are drawn and sorted into the two cases; each is checked, the owner test with both
owner-needs conventions ('bundle' = Lean's Output, 'base').
With --relabel: the contrast depends on the labeling. For t <= T, on every relabeling of the agents of H_t (up to K
random ones when there are more), l is inserted first and index order follows; counts the relabelings on which some
y_j takes e_j (k4/adaptive.md §3, remark after Step 1).
Usage: adaptive_verify_H.py T K [--seed=S] [--backend=sat|milp] [--relabel]   (C4VERIFY_DIR: the folder with
lb4r.py, hcore.py; default k4/c4_verify_H, from PR #33)"""
import itertools, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get('C4VERIFY_DIR') or os.path.join(HERE, 'c4_verify_H'))
from hcore import build_H
from lb4r import Inst, phase1_state, up_run, all_needs, output_sat, output_check

def relabel(T, K, seed):
    for t in range(1, T + 1):
        agents, goods, v = build_H(t); n = len(agents)
        gi = {g: k for k, g in enumerate(goods)}
        e = {j: gi[f'g{j + 1}'] if j < t else gi['z'] for j in range(1, t + 1)}
        rng = random.Random(seed * 100 + t)
        exhaustive = len(list(itertools.islice(itertools.permutations(range(n)), K + 1))) <= K
        perms = itertools.permutations(range(n)) if exhaustive else (rng.sample(range(n), n) for _ in range(K))
        tot = casc = 0
        for p in perms:                          # new agent i is old agent p[i]
            inst = Inst([v[p[i]] for i in range(n)])
            new = {p[i]: i for i in range(n)}
            name = lambda a: new[agents.index(a)]
            s0, _ = phase1_state(inst, [name('l')] + [0] * n)
            tot += 1; casc += any(s0[1][name(f'y{j}')] == e[j] for j in range(1, t + 1))
        print(f"H_{t}: {tot} {'(every)' if exhaustive else 'random'} relabelings, l inserted first and index order after "
              f"it: some y_j takes e_j (cascade) in {casc}", flush=True)

def main():
    T, K = int(sys.argv[1]), int(sys.argv[2])
    seed = int(next((a.split('=')[1] for a in sys.argv[3:] if a.startswith('--seed=')), 1))
    backend = next((a.split('=')[1] for a in sys.argv[3:] if a.startswith('--backend=')), 'sat')
    print('# adaptive_verify_H.py', ' '.join(sys.argv[1:]), flush=True)
    if '--relabel' in sys.argv[3:]: relabel(T, K, seed); return
    for t in range(1, T + 1):
        agents, goods, v = build_H(t)
        inst = Inst(v); n = inst.n
        gi = {g: k for k, g in enumerate(goods)}
        ai = {a: k for k, a in enumerate(agents)}
        gad1 = {ai['x11'], ai['x12'], ai['x13'], ai['y1']}
        e = [gi[f'g{j + 1}'] if j < t else gi['z'] for j in range(1, t + 1)]
        rng = random.Random(seed * 100 + t)
        stats = {'good': 0, 'good_ok': 0, 'bad': 0, 'bad_cascade': 0}
        for k in range(K):
            first = rng.randrange(n) if k % 2 else rng.choice(sorted(gad1))   # half the draws start in gadget 1
            tau = [first] + [rng.randrange(n) for _ in range(n)]
            s0, run = phase1_state(inst, tau)
            order = [x for x, f, kind in run]
            touched_first = min(order.index(a) for a in gad1) < order.index(ai['l'])
            cascade = any(s0[1][ai[f'y{j}']] == e[j - 1] for j in range(1, t + 1))
            if not touched_first:
                stats['bad'] += 1; stats['bad_cascade'] += cascade
                continue
            stats['good'] += 1
            assert not cascade, (t, tau)
            s1, _ = up_run(inst, s0, 'shrink')
            needs = all_needs(inst, s1)
            assert not any(needs), (t, tau, 'a need survives the upgrades')
            marked = s1[2]
            r = max((i for i in range(n) if not marked[i]), key=lambda i: order.index(i))
            ok = True
            for conv in ('bundle', 'base'):
                good, X = output_sat(inst, s1, r, conv, needs, want_model=True, backend=backend)
                ok = ok and good and output_check(inst, s1, r, X, conv, needs)
            assert ok, (t, tau, 'owner r has no output')
            stats['good_ok'] += 1
        print(f"H_{t}: {K} sequences; gadget 1 touched before l: {stats['good']}, all checks hold in "
              f"{stats['good_ok']} (no cascade, NA empty after need-shrinking upgrades, owner r has an output under both "
              f"conventions); l first: {stats['bad']}, of which y_1 takes e_1 in {stats['bad_cascade']}", flush=True)

if __name__ == '__main__':
    main()
