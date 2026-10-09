"""Candidate rotation-free algorithms from reductions to solved cases (NOTES.md). EVIDENCE only.
Each candidate maps (rank, m) to X (X[g] = owner) or None (gives up). `python3 candidates.py NAME... [--big]` runs
the exhaustive protocol and prints, per (n, m), the number of profiles that are not EFX0 and the first failing one.
"""
import sys, itertools, time
from engine import (k3s_like, ok, gen_small, vals, leader_index_top, leader_index_pair, leader_hub_top,
                    leader_pair_safe, leader_pair_c_only, NA)

# ---------------------------------------------------------------------------------- idea 1: drop one good per agent
def sd2(rank, m, keep):
    """serial dictatorship in index order on the 2-good instance keep[i] (a ranked pair of agent i's goods);
    returns the picks Y and the leftover goods"""
    free = set(range(m)); Y = [None] * len(rank)
    for i, ks in enumerate(keep):
        Y[i] = next((g for g in ks if g in free), None); free.discard(Y[i])
    return Y, free

def ignore_c(rank, m):
    """Corollary L2c verbatim on the instance where every agent ignores its c: SD, the last agent takes the rest"""
    Y, free = sd2(rank, m, [r[:2] for r in rank])
    X = [None] * m
    for i, g in enumerate(Y):
        if g is not None: X[g] = i
    for g in free: X[g] = len(rank) - 1
    return X

def ignore_most_valued(rank, m):
    """every agent ignores whichever of b, c has more valuers (ties: c); then L2c"""
    cnt = lambda g: sum(g in r for r in rank)
    keep = [(r[0], r[1]) if cnt(r[2]) >= cnt(r[1]) else (r[0], r[2]) for r in rank]
    Y, free = sd2(rank, m, keep)
    X = [None] * m
    for i, g in enumerate(Y):
        if g is not None: X[g] = i
    for g in free: X[g] = len(rank) - 1
    return X

def ignore_c_repair(rank, m):
    """ignore c, SD, then one simple repair pass, no upgrades/rotation:
    (1) an agent holding nothing takes its c if free; (2) an agent holding its top whose b and c are both left over
    takes c if nobody needs its top alone; (3) the last free agent (nobody needs its pick alone) takes the rest"""
    n = len(rank); Y, free = sd2(rank, m, [r[:2] for r in rank]); extra = [[] for _ in range(n)]
    for i in range(n):
        if Y[i] is None and rank[i][2] in free: Y[i] = rank[i][2]; free.discard(Y[i])
    na = NA(rank, Y, [])
    for i in range(n):
        if Y[i] == rank[i][0] and rank[i][1] in free and rank[i][2] in free and Y[i] not in na:
            extra[i].append(rank[i][2]); free.discard(rank[i][2])
    fr = [i for i in range(n) if Y[i] is None or Y[i] not in na]
    o = fr[-1] if fr else n - 1
    X = [None] * m
    for i in range(n):
        if Y[i] is not None: X[Y[i]] = i
        for g in extra[i]: X[g] = i
    for g in free: X[g] = o
    return X

# ---------------------------------------------------------------------------------- K3S steps 1-3 with plug-ins
def mk(leader, absorber):
    return lambda rank, m: k3s_like(rank, m, leader, absorber)

CANDS = {
    'ignore_c': ignore_c,
    'ignore_most_valued': ignore_most_valued,
    'ignore_c_repair': ignore_c_repair,
    'k3s_norot_r': mk(leader_index_top, 'r'),            # baseline (K3S without rotation)
    'k3s_norot_any': mk(leader_index_top, 'any'),        # ... with a search over the absorber
    'hub_r': mk(leader_hub_top, 'r'),                    # idea 2: hubs first
    'hub_any': mk(leader_hub_top, 'any'),
    'pair_r': mk(leader_index_pair, 'r'),                # leaders take {b, c} instead of a
    'pair_any': mk(leader_index_pair, 'any'),
    'pairsafe_r': mk(leader_pair_safe, 'r'),
    'pairsafe_any': mk(leader_pair_safe, 'any'),
    'pairc_r': mk(leader_pair_c_only, 'r'),
    'pairc_any': mk(leader_pair_c_only, 'any'),
}

SMALL = [(2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5)]
BIG = [(4, 6)]

def run(name, sets, stop_after_first=False):
    f = CANDS[name]; t = time.time(); out = []
    for n, m in sets:
        tot = bad = 0; first = None
        for rank in gen_small(n, m):
            tot += 1
            if not ok(rank, m, f(rank, m)):
                bad += 1
                if first is None: first = rank
        out.append((n, m, tot, bad, first))
        print(f"{name:20s} n={n} m={m}: {bad} of {tot} not EFX0; first {first}  [{time.time() - t:.0f}s]", flush=True)
        if stop_after_first and bad: break
    return out

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    sets = SMALL + (BIG if '--big' in sys.argv else [])
    for name in (args or list(CANDS)):
        run(name, sets, stop_after_first='--stop' in sys.argv)
