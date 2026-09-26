"""Replay the failed approaches of k4/c4one.md (attempts/k4-c4one-*.md).

one-rotation: Conjecture C4^1 as stated in k4/c4.md §6.2 (at most one 4-good agent: after upgrades some owner or one
rotation works, for every run of Phase 1) is false at n = 5. The index-order run of the core
[[0,3,7],[1,5,8],[2,6,7,8],[3,4,5],[4,6,8]] with values [[2,3,4],[2,4,3],[2,3,8,4],[2,3,4],[4,2,3]] has no valid owner
and no single rotation that works, under each upgrade policy, with the owner's needs from its base or its bundle, and
with or without a slot for a rotated agent's one-good base (checked with the independent tracer
k4/c4tools/c4trace.py); two nested rotations work; the profile has 167 EFX0 allocations with at most one bundle of
more than 2 goods (brute force, k4/lb4_brute.py). lb4.c agrees: -i0 -u3 -o0 -r1 -w1 -c1 fails on 4 profiles of this
core, -r2 on none; with every insertion sequence the core [[0,2,4,7],[1,2,3],[1,5,6],[3,5,7],[4,6,7]] (m = 8) fails too.
potential (attempts/k4-c4one-potential.md): route 2's local step, "whenever no owner is valid, some rotation strictly
raises the count" (Phi = the best A4+ slack over owners, or the owner-free count), fails on these two states.
realization (attempts/k4-c4one-realization.md): in case (Tc), inserting q at the start of its block reproduces the
rotation along a need chain from the old leader to q in every case at n <= 4, but not always at n = 5.
Usage: python3 attempts/k4_c4one_attempts.py [NAME ...]   (default: all)"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
K4 = os.path.join(HERE, '..', 'k4')
sys.path.insert(0, os.path.join(K4, 'c4tools')); sys.path.insert(0, K4)
from c4trace import *
import lb4_brute, lb4_run

def lb4(opts, m, sets):
    lb4_run.build()
    p = subprocess.run([lb4_run.BIN] + opts.split() + ['-f0'], input=lb4_run.encode(sets, m, False),
                       capture_output=True, text=True, check=True)
    tot = next(l for l in p.stdout.splitlines() if l.startswith('total')).split()   # lb4.c prints an 'H ...' line first
    return int(tot[tot.index('fails') + 1]), int(tot[1])

def one_rotation():
    sets = [[0, 3, 7], [1, 5, 8], [2, 6, 7, 8], [3, 4, 5], [4, 6, 8]]
    vals = [[2, 3, 4], [2, 4, 3], [2, 3, 8, 4], [2, 3, 4], [4, 2, 3]]
    I = Inst(sets, vals)
    st0 = initial_state(I, [])[0]
    print('one rotation: n = 5, m = 9, one 4-good agent (agent 2), index insertion'); print(pretty(st0))
    ok = True
    for mode in (1, 2, 0):
        st = upgrades(st0, mode)
        owner = any(try_owners(st, w1=w1, rot_slot=rs) is not None for w1 in (False, True) for rs in (False, True))
        one = sum(len(search(st, 1, w1=w1, rot_slot=rs)) for w1 in (False, True) for rs in (False, True))
        two = len(search(st, 2, w1=True, rot_slot=True, all_paths=False)) > 0
        print(f'   upgrade policy {mode}: some owner works: {owner}; single rotations that work: {one}; '
              f'two nested rotations work: {two}')
        ok &= not owner and one == 0 and two
    sols = [X for X in lb4_brute.all_efx0(sets, vals) if sum(len(B) > 2 for B in X) <= 1]
    print(f'   brute force: {len(sols)} EFX0 allocations with at most one bundle of more than 2 goods, e.g. {sols[0]}')
    ok &= len(sols) > 0
    for m, S, opts, want in [(9, sets, '-i0 -u3 -o0 -r1 -w1 -c1', True), (9, sets, '-i0 -u3 -o0 -r2 -w1 -c1', False),
                             (8, [[0, 2, 4, 7], [1, 2, 3], [1, 5, 6], [3, 5, 7], [4, 6, 7]], '-i1 -u3 -o0 -r1 -w1 -c1', True),
                             (8, [[0, 2, 4, 7], [1, 2, 3], [1, 5, 6], [3, 5, 7], [4, 6, 7]], '-i1 -u3 -o0 -r2 -w1 -c1', False)]:
        f, t = lb4(opts, m, S)
        print(f'   lb4.c {opts} on m = {m} core {S}: {f} of {t} (run, profile) pairs fail')
        ok &= (f > 0) == want
    return ok

def potential():
    """route 2: from a state with no valid owner, no single rotation raises Phi (nor the owner-free count)"""
    from c4pot import Phi, count
    ok = True
    for what, sets, vals, tau in [
            ('two 4-good agents (agents 0, 1), n = 3, m = 6, first insertion agent 2',
             [[0, 1, 2, 5], [2, 3, 4, 5], [3, 4, 5]], [[1, 4, 8, 6], [8, 2, 3, 4], [2, 3, 4]], [2]),
            ('one 4-good agent (agent 2), n = 5, m = 9, index insertion',
             [[0, 3, 7], [1, 5, 8], [2, 6, 7, 8], [3, 4, 5], [4, 6, 8]], [[2, 3, 4], [2, 4, 3], [2, 3, 8, 4], [2, 3, 4], [4, 2, 3]], [])]:
        I = Inst(sets, vals)
        st = upgrades(initial_state(I, tau)[0], 2)
        print(f'potential: {what}'); print(pretty(st))
        f0, c0 = Phi(st), count(st)
        rots = []
        fr = st.frozen()
        for k in range(I.n):
            if not fr[k]: continue
            for ch in chains_from(st, k):
                for O in rot_options(st, ch):
                    ns = rotate(st, ch, O)
                    if ns.valid(): rots.append((tuple(ch), sorted(O), Phi(ns), count(ns)))
        print(f'   no valid owner: {try_owners(st, w1=True, rot_slot=True) is None}; Phi {f0}, count {c0}')
        for ch, O, f, c in rots: print(f'   rotation {ch} O = {O}: Phi {f}, count {c}')
        two = len(search(st, 2, w1=True, rot_slot=True, all_paths=False)) > 0
        print(f'   two nested rotations reach a valid owner: {two}')
        ok &= try_owners(st, w1=True, rot_slot=True) is None and all(f <= f0 and c <= c0 for _, _, f, c in rots) and two
    return ok

def realization():
    """k4/c4one.md §6 (a): inserting q at the start of its block need not reproduce the rotation along a need chain from
    the old leader to q, even in case (Tc) (attempts/k4-c4one-realization.md)"""
    sets = [[0, 1, 3, 4], [2, 3, 6], [2, 6, 7], [4, 5, 7], [5, 6, 7]]
    vals = [[2, 4, 3, 8], [3, 2, 4], [4, 2, 3], [4, 2, 3], [2, 4, 3]]
    I = Inst(sets, vals); q, ell = 0, 3
    old = upgrades(initial_state(I, [3, 2])[0], 2)    # leaders 3, then 4
    new = upgrades(initial_state(I, [0])[0], 2)       # q inserted first, then index order
    print('realization: n = 5, m = 8, q = agent 0; old run (leaders 3, 4):'); print(pretty(old))
    print('   new run (q inserted at the start of its block, which is the first block):'); print(pretty(new))
    Y, Y2 = old.Y, new.Y
    rotations = []
    for ch in chains_from(old, ell):
        if ch[-1] != q: continue
        pred = list(Y)
        for k in range(1, len(ch)): pred[ch[k]] = Y[ch[k - 1]]
        rotations.append((ch, [i for i in range(I.n) if i != ell and Y2[i] != pred[i]]))
    for ch, off in rotations: print(f'   rotation along {ch}: the new picks differ at agents {off}')
    pulled = [z for z in range(I.n) if Y2[ell] in I.R[z] and z != ell and old.blk[z] > old.blk[q]]
    print(f'   the old leader {ell} takes {Y2[ell]} (its b); agents of a later block with that good: {pulled}')
    print(f'   omega: old {old.omega()}, new {new.omega()}')
    return bool(rotations) and all(off for _, off in rotations) and bool(pulled) and new.omega() >= old.omega()

ALL = {'one-rotation': one_rotation, 'potential': potential, 'realization': realization}

if __name__ == '__main__':
    names = sys.argv[1:] or list(ALL)
    res = {nm: ALL[nm]() for nm in names}
    print('\n' + '\n'.join(f'{nm}: {"reproduced" if v else "NOT reproduced"}' for nm, v in res.items()))
    sys.exit(0 if all(res.values()) else 1)
