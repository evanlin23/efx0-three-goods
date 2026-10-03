"""Experiment 4: which case of the stuck lemma occurs (NOTES.md §4). Evidence only.

For every stuck valid state (no up / cycle / rot move, exp_local.py) with overflow > 0, classify:
  E   some agent holds nothing (absorber = that agent; proved: nobody is exposed for it)
  F1  no agent holds nothing and at most one free agent (proved: nobody is exposed for it / for a pair holder)
  F2+ no agent holds nothing and at least two free agents (open): record min over free o of |E_o| - (|F| - 1),
      and whether some free agent has E_o empty.
Also checks claim S1 (no agent holds a_x with b_x and c_x both left over) on every stuck state.

  python3 exp_stuck_cases.py small N M | random K SEED MAXN
"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
from common import Base
from exp_fast import valid_states
from exp_local import one_moves

def run(rank, m, st, first):
    for opt, _, _ in valid_states(rank, m):
        if one_moves(rank, m, opt): continue
        b = Base(rank, m, opt); J = set(b.J)
        s1 = any(opt[x] == 1 and rank[x][1] in J and rank[x][2] in J for x in range(b.n))
        st['S1_violated'] += s1
        if s1 and 'S1' not in first: first['S1'] = (rank, m, opt)
        if b.overflow() <= 0: continue
        if 0 in opt: st['E'] += 1; continue
        F = [i for i in b.free]
        if len(F) <= 1: st['F1'] += 1; continue
        st['F2+'] += 1
        d = min(len(b.exposed(o)) - (len(F) - 1) for o in F)
        st[f'F2+ min deficit {d}'] += 1
        st['F2+ some free o with E_o empty'] += any(not b.exposed(o) for o in F)
        if not any(not b.exposed(o) for o in F) and 'F2_nonempty' not in first: first['F2_nonempty'] = (rank, m, opt)

if __name__ == '__main__':
    from test_k3s import gen_small
    st = collections.Counter(); first = {}
    if sys.argv[1] == 'small':
        n, m = int(sys.argv[2]), int(sys.argv[3])
        for _, _, r in gen_small(n, m): run(r, m, st, first)
        print(f"small n={n} m={m}: {dict(st)}")
    else:
        K, seed, N = map(int, sys.argv[2:5]); rng = random.Random(seed)
        for _ in range(K):
            n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 3)
            run([tuple(rng.sample(range(m), 3)) for _ in range(n)], m, st, first)
        print(f"random K={K} seed={seed} n<={N}: {dict(st)}")
    for k, v in first.items(): print("  first", k, v)
