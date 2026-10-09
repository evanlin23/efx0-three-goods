"""Experiment 3: a LOCAL optimality condition instead of the rotation. Evidence only.

Moves on a valid base state (each keeps it valid and makes every agent it touches strictly better, so the sum of
utilities nothing < c < b < a < {b, c} grows and repeated moves stop):
  up(k)        k holds b_k, c_k is junk, nobody needs b_k: k takes {b_k, c_k}   (K3S step 2)
  rot(x, chain) x holds a_x and gives it up for {b_x, c_x}; a_x goes to an agent j_1 that needs it, j_1's good to an
               agent j_2 that needs it, ..., (any length, possibly 0); b_x and c_x must be junk or the good released
               at the end; the result must be valid (the released good, if x does not take it, is needed by nobody)
A state is *stuck* if no move applies. Claim tested: every stuck valid state completes (absorber + slot filling).
Also counted: absorber rules on stuck states.

  python3 exp_local.py small N M | cores MAXN SAMPLE MINN | random K SEED MAXN
"""
import sys, os, collections, random
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
from common import Base, held
from exp_fast import valid_states

def one_moves(rank, m, opt):
    n = len(rank); b = Base(rank, m, opt); J = set(b.J); NA = b.NA
    Y = [held(rank[i], opt[i]) for i in range(n)]
    out = []
    for k in range(n):
        if opt[k] == 2 and rank[k][2] in J and rank[k][1] not in NA:
            o2 = list(opt); o2[k] = 4; out.append(('up', k, tuple(o2)))
    def needs(j, g):
        return opt[j] in (0, 2, 3) and g in rank[j] and (opt[j] == 0 or rank[j].index(g) < opt[j] - 1)
    # trading cycles among agents holding one good: each takes the next one's good, which it needs
    singles = [j for j in range(n) if opt[j] in (2, 3)]
    def cyc(path):
        for j in singles:
            if not needs(path[-1], Y[j][0]): continue
            if j == path[0]:
                o2 = list(opt)
                for s, i in enumerate(path):
                    o2[i] = rank[i].index(Y[path[(s + 1) % len(path)]][0]) + 1
                out.append(('cycle', tuple(path), tuple(o2)))
            elif j not in path and j > path[0]:
                cyc(path + [j])
    for j0 in singles: cyc([j0])
    for x in range(n):
        if opt[x] != 1: continue
        bx, cx = rank[x][1], rank[x][2]
        # DFS over chains
        def dfs(chain, g):
            # g = good currently passed along (released by the last agent of chain, or a_x)
            # option A: stop here; g is released
            avail = J | {g}
            if bx in avail and cx in avail:
                o2 = list(opt); o2[x] = 4
                for s in range(1, len(chain)):
                    prev = chain[s - 1]; j = chain[s]
                    gg = rank[x][0] if s == 1 else Y[prev][0]
                    o2[j] = rank[j].index(gg) + 1
                if Base(rank, m, tuple(o2)).valid: out.append(('rot', tuple(chain), tuple(o2)))
            for j in range(n):
                if j in chain or not needs(j, g): continue
                if opt[j] == 0:
                    # j takes g and releases nothing: the chain ends
                    o2 = list(opt); o2[x] = 4
                    ch = chain + [j]
                    if bx in J and cx in J:
                        for s in range(1, len(ch)):
                            prev = ch[s - 1]; jj = ch[s]
                            gg = rank[x][0] if s == 1 else Y[prev][0]
                            o2[jj] = rank[jj].index(gg) + 1
                        if Base(rank, m, tuple(o2)).valid: out.append(('rot', tuple(ch), tuple(o2)))
                    continue
                dfs(chain + [j], Y[j][0])
        dfs([x], rank[x][0])
    return out

def run_profile(rank, m, stats, first):
    sts = valid_states(rank, m)
    for opt, _, _ in sts:
        b = Base(rank, m, opt)
        mv = one_moves(rank, m, opt)
        if mv: continue
        stats['stuck'] += 1
        cands = [i for i in range(b.n) if i in b.free or opt[i] == 4]
        ok = [o for o in cands if b.complete(o) is not None]
        if b.overflow() <= 0: stats['stuck_fits'] += 1
        if ok:
            stats['stuck_completes'] += 1
            from common import efx0_rank
            assert efx0_rank(rank, m, b.complete(ok[0]))
            if b.overflow() > 0:
                stats['stuck_needs_absorber'] += 1
                # simple absorber rules
                if any(opt[o] == 0 for o in ok) or not any(opt[o] == 0 for o in cands): pass
                r1 = max(cands, key=lambda o: (opt[o] == 4, opt[o]))     # prefer pair holders, then worst holding
                stats['rule_worst_holding_ok'] += r1 in ok
                r2 = min(cands, key=lambda o: len(b.exposed(o)))
                stats['rule_min_exposed_ok'] += r2 in ok
                r3 = [o for o in cands if opt[o] != 4]
                stats['rule_nonpair_exists'] += any(o in ok for o in r3)
        else:
            stats['stuck_fails'] += 1
            if 'stuck_fails' not in first: first['stuck_fails'] = (len(rank), m, rank, opt)

if __name__ == '__main__':
    from test_k3s import gen_small
    from lbx import core_profiles
    mode = sys.argv[1]; stats = collections.Counter(); first = {}; tot = 0
    if mode == 'small':
        n, m = int(sys.argv[2]), int(sys.argv[3]); src = ((r, m) for _, _, r in gen_small(n, m)); title = f"small n={n} m={m}"
    elif mode == 'cores':
        N, S, lo = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        src = ((r, m) for _, m, r in core_profiles(N, sample=S, minn=lo)); title = f"cores n in [{lo},{N}] sample={S}"
    else:
        K, seed, N = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]); rng = random.Random(seed)
        def gen():
            for _ in range(K):
                n = rng.randint(2, N); m = rng.randint(max(3, n), 2 * n + 3)
                yield [tuple(rng.sample(range(m), 3)) for _ in range(n)], m
        src = gen(); title = f"random K={K} seed={seed} n<={N}"
    for rank, m in src:
        run_profile(rank, m, stats, first); tot += 1
    print(f"{title}: {tot} profiles; {dict(stats)}")
    for k, v in first.items(): print(f"  first {k}: {v}")
