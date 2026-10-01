#!/usr/bin/env python3
"""Replays the failed statements of proof/k4-dl2-k1 (k4/dl2.md; attempts/k4-dl2-*.md) with two implementations.

1. Conjecture DL2 (k4/strategy.md §3, ledger K4.STRAT.DL2) fails at n = 3, m = 7 (attempts/k4-dl2-three-agents.md):
   a min-frozen P with def(P) = 1 whose nearest min-frozen P' with a smaller deficit differs from P in all three
   agents' bases.
   Implementation A: k4/suite/model.py (the suite's model; deficit_local.kstar).
   Implementation B: k4/c4x_check.py (main's independent checker of k4/c4x.c: it enumerates every base map good ->
   agent or junk, validity (V1), (V2) literally, and its own removal-only deficit `rodef`).
2. The failed lemma versions of k4/dl2.md (each with its smallest failing configuration), with implementation A and
   the brute-force deficit of k4/dl2_classify.py's Lemma H1 formula (asserted equal to model.Inst.deficit).
usage: python3 attempts/k4_dl2_attempts.py"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'suite'))
sys.path.insert(0, os.path.join(ROOT, 'k4'))
import model as M
import deficit_local as DLc
import c4x_check as CX

ok_all = True


def say(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print('%-62s %s  %s' % (name, 'confirmed' if ok else 'NOT REPRODUCED', detail), flush=True)


def kstar_B(sets, vals, m):
    """k* with implementation B: c4x_check.analyse enumerates 𝒫 with rodef; min-frozen = most '-frozen'"""
    vals_list = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    res = CX.analyse(sets, m, vals_list)
    mf = max(r[2]['-frozen'] for r in res)
    mp = [(tuple(r[0]), r[2]['rodef']) for r in res if r[2]['-frozen'] == mf]
    worst, per = 0, {}
    for Bs, d in mp:
        if d <= 0: continue
        dist = min((sum(1 for a, b in zip(Bs, B2) if a != b) for B2, d2 in mp if d2 < d), default=None)
        per[tuple(tuple(sorted(B)) for B in Bs)] = (d, dist)
        worst = max(worst, dist if dist is not None else 99)
    return worst, per, len(mp)


# 1. DL2 at n = 3, m = 7 (gap_n3 record core 0 of results/k4_certs_3.json.gz, profile 10,23,219 of #53's catalogue)
sets = [[0, 1, 2, 3], [2, 4, 5, 6], [3, 4, 5, 6]]
vals = [[2, 4, 3, 8], [2, 6, 10, 7], [8, 3, 4, 2]]
m = 7
I = M.Inst(sets, vals, m)
I.preallocs()
core_ok = I.core_violations() == [] and I.strict()
kA, detA = DLc.kstar({'sets': sets, 'vals': vals, 'm': m})
kB, perB, nB = kstar_B(sets, vals, m)
P0 = ((3,), (2, 5), (4, 6))
B0 = tuple(M.mask(b) for b in P0)
dA = I.deficit(B0)
mpA = [Bs for Bs, NA in I.minP]
distA = min(sum(1 for a, b in zip(B0, B2) if a != b) for B2 in mpA
            if (lambda x: 10 ** 9 if x is None else x)(I.deficit(B2)) < dA)
say('DL2 fails: n = 3, m = 7 core, k* = 3 (dl2-n3m7)', core_ok and kA == 3 and kB == 3 and dA == 1 and distA == 3
    and perB.get(P0) == (1, 3),
    'core %s; k* model/c4x_check: %s/%s; P0 = %s: def %s, distance %s (B: %s); %d min-frozen P (B: %d)' % (
        core_ok, kA, kB, list(map(list, P0)), dA, distA, perB.get(P0), len(mpA), nB))

if __name__ == '__main__':
    print('all confirmed' if ok_all else 'SOME CHECK NOT REPRODUCED')
    sys.exit(0 if ok_all else 1)
