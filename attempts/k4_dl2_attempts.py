#!/usr/bin/env python3
"""Replays the failed statements of proof/k4-dl2-k1 (k4/dl2.md; attempts/k4-dl2-*.md) with two implementations.

1. Conjecture DL2 (k4/strategy.md §3, ledger K4.STRAT.DL2) fails at n = 3, m = 7 (attempts/k4-dl2-three-agents.md):
   a min-frozen P with def(P) = 1 whose nearest min-frozen P' with a smaller deficit differs from P in all three
   agents' bases.
   Implementation A: k4/suite/model.py (the suite's model; deficit_local.kstar).
   Implementation B: k4/c4x_check.py (main's independent checker of k4/c4x.c: it enumerates every base map good ->
   agent or junk, validity (V1), (V2) literally, and its own removal-only deficit `rodef`).
2. The structured relations R of k4/dl2.md §3 for which DL_R fails (attempts/k4-dl2-relations.md), each at its
   smallest failing state found: implementation A is k4/dl2_relations.py (shapes of every improving move, on
   k4/suite/model.py), implementation B is c4x_check.analyse with membership tests written separately here. At each
   such state both implementations also find a move of R_T (DL_T holds there).
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


# 2. Relations R of k4/dl2.md §3 for which DL_R fails (attempts/k4-dl2-relations.md).
#    Implementation A: k4/dl2_relations.py (shapes of the moves on k4/suite/model.py's 𝒫 and deficit).
#    Implementation B: c4x_check.analyse (its own 𝒫 and rodef) with the membership tests below, written separately.
import dl2_relations as DR


def rel_B(name, sets, vals, P, P2):
    """does P -> P2 belong to relation `name`? (bases: tuples of frozensets; written independently of DR.shape)"""
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    val = lambda i, B: sum(vl[i].get(g, 0) for g in B)
    nd = lambda i, B: frozenset(g for g in vl[i] if g not in B and vl[i][g] > val(i, B))
    N1 = [nd(i, P[i]) for i in range(len(P))]; N2 = [nd(i, P2[i]) for i in range(len(P))]
    NA1 = frozenset().union(*N1); NA2 = frozenset().union(*N2)
    fz1 = [len(B) == 1 and B <= NA1 for B in P]; fz2 = [len(B) == 1 and B <= NA2 for B in P2]
    ch = [i for i in range(len(P)) if P[i] != P2[i]]
    if name == 'RT' and len(ch) == 1: return NA1 == NA2         # R_T's re-bases keep the needed set
    if len(ch) == 1: return True                                  # one re-base: in every other relation tested
    trade = len(ch) == 2 and NA1 == NA2 and not any(fz1[i] or fz2[i] for i in ch)
    xs = [i for i in ch if fz1[i] and not fz2[i]]; zs = [i for i in ch if fz2[i] and not fz1[i]]
    ws = [i for i in ch if fz1[i] and fz2[i]]; ys = [i for i in ch if not fz1[i] and not fz2[i]]
    swap = (len(xs) == 1 and len(zs) == 1 and not ws and NA1 == NA2 and P2[zs[0]] == P[xs[0]]
            and P[xs[0]] <= N1[zs[0]])
    rel1 = all(P2[y] < P[y] and len(P[y] - P2[y]) == 1 for y in ys)
    rel = all(P2[y] < P[y] for y in ys)
    if name == 'RB2': return trade or (swap and not ys)
    if name == 'RS1+2': return trade or (swap and rel1)
    if name == 'RSR+2': return trade or (swap and rel)
    if name == 'RSY': return swap and len(ys) <= 1
    if name == 'RSYa': return swap
    if name == 'RSYgz+2':                 # the helper gives up a good and takes goods only from its base and B_z
        return trade or (swap and len(ys) <= 1 and all(P[y] - P2[y] and P2[y] <= P[y] | P[zs[0]] for y in ys))
    if name == 'RT':                      # R_T: exchanging trades; swaps with at most one helper giving up a good
        exch = trade and (P2[ch[0]] & P[ch[1]] or P2[ch[1]] & P[ch[0]])
        return bool(exch) or (swap and len(ys) <= 1 and all(P[y] - P2[y] for y in ys))
    if name == 'RC':                      # a chain of frozen goods ending at a free agent, releasing helpers
        if len(xs) != 1 or len(zs) != 1 or NA1 != NA2 or not rel: return trade
        src = {P[i] for i in xs + ws}
        return trade or all(P2[i] in src for i in ws + zs)
    raise ValueError(name)


def relation_fails(label, sets, vals, m, P0, names, smallest=''):
    """state P0 (lists of goods) has def > 0 and no min-frozen neighbour with a smaller deficit in each relation, by
    both implementations"""
    d = {'sets': sets, 'vals': vals, 'm': m}
    I = M.Inst(sets, vals, m); core = I.core_violations() == [] and I.strict()
    stA = [r for r in DR.profile(d) if r['Bs'] == [sorted(b) for b in P0]]
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    res = CX.analyse(sets, m, vl)
    mf = max(r[2]['-frozen'] for r in res)
    mp = [(tuple(r[0]), r[2]['rodef']) for r in res if r[2]['-frozen'] == mf]
    PB = tuple(frozenset(b) for b in P0)
    dB = dict(mp).get(PB)
    for nm in names:
        a = bool(stA) and stA[0]['def'] > 0 and stA[0]['holds'][nm] is False
        b = dB is not None and dB > 0 and not any(d2 < dB and rel_B(nm, sets, vals, PB, B2) for B2, d2 in mp)
        say('DL_%s fails: %s' % (nm, label), core and a and b,
            'core %s; P0 = %s def %s (B: %s); model / c4x_check: no %s-neighbour with a smaller deficit: %s / %s%s' % (
                core, [sorted(b) for b in P0], stA[0]['def'] if stA else None, dB, nm, a, b, smallest))
    # and R_T holds there, by both implementations
    a = bool(stA) and stA[0]['holds']['RT'] is True
    b = dB is not None and any(d2 < dB and rel_B('RT', sets, vals, PB, B2) for B2, d2 in mp)
    say('   ... while DL_T holds at the same state', a and b, 'model / c4x_check: %s / %s' % (a, b))


# 2a. no trades (two free agents re-basing): DL_RSY, DL_RSYa fail at n = 2, m = 5, f = 0 (suite instance induct-g-r1,
#     #43): no frozen agent, so no role swap; only the exchange of goods 2 and 3 between the two agents helps
relation_fails('n = 2, m = 5, f = 0 (induct-g-r1)', [[0, 2, 3, 4], [1, 2, 3, 4]], [[4, 10, 8, 3], [4, 8, 10, 3]], 5,
               [[0, 3], [1, 2]], ['RSY', 'RSYa'])
# 2b. moves of at most two agents (DL2 with role swaps and trades): DL_RB2 fails at dl2-n3m7
relation_fails('n = 3, m = 7 (dl2-n3m7)', sets, vals, m, [[3], [2, 5], [4, 6]], ['RB2'])
# 2c. helpers that only give up goods: DL_RS1+2, DL_RSR+2, DL_RC fail at n = 3, m = 7 (#53's n = 3 catalogue, core 0 of
#     results/k4_certs_3.json.gz, profile 10,57,227): the helper must also take a good of the needer's old base
relation_fails('n = 3, m = 7 (dl2-n3m7-trade)', [[0, 1, 2, 3], [2, 4, 5, 6], [3, 4, 5, 6]],
               [[2, 4, 3, 8], [3, 6, 7, 5], [8, 4, 2, 3]], 7, [[3], [2, 4], [5, 6]], ['RS1+2', 'RSR+2', 'RC'])
# 2d. a helper restricted to its own base and the needer's old base: DL_RSYgz+2 fails at n = 3, m = 8 (core 4 of
#     results/k4_certs_3.json.gz, profile 14,112,152): the helper must take a junk good
relation_fails('n = 3, m = 8 (dl2-n3m8-junk)', [[0, 2, 4, 5], [1, 4, 6, 7], [3, 5, 6, 7]],
               [[2, 4, 8, 3], [4, 8, 3, 2], [6, 3, 5, 7]], 8, [[4], [1], [3, 5]], ['RSYgz+2'])

if __name__ == '__main__':
    print('all confirmed' if ok_all else 'SOME CHECK NOT REPRODUCED')
    sys.exit(0 if ok_all else 1)
