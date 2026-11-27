"""Who does Z = {Y'_k, Y'_d} + (J' - S) threaten after DEMOTE-2's first step (k4/oc1_hall.md §24.11)?  Every 10th
DEMOTE-2 start of the n = 5 export partial6 (compute/k4-oc1max-cert), the first k of D_T' whose chain "k takes S, d
takes Y'_k" is official: the agents Z threatens at their values after the chain (by role: k', u = the old receiver,
on/off the RF path), and whether giving one good g of Z - {Y'_k} to k' instead gives an EFX0 allocation (raw).

    python3 k4/oc1_hall/rf_bpp.py   (reads the export from SP below; see rf_n5.py for how to fetch it)
"""
import sys, os, json, gzip, collections, itertools, multiprocessing as mp
sys.path.insert(0, 'k4/oc1_hall')
from ohlib import Inst, picks, Picks, threatened, base_of_picks, bundles_of, efx0, frozen_set
from greedy_rules import apply_chain
SP = '/tmp/claude-0/-home-user-efx0-three-goods/14af45a0-d875-5f15-80f8-d31748dc8506/scratchpad/n5data/'
def job(task):
    sets, starts = task; m = 1 + max(max(s) for s in sets); C = collections.Counter(); seen = set(); cnt = 0
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]
        for o in st['orders']:
            Y2 = picks(I, [u] + [x for x in o if x != u])
            if None in Y2 or (json.dumps(vals), Y2) in seen: continue
            seen.add((json.dumps(vals), Y2)); P = Picks(I, Y2)
            U2 = [i for i in range(I.n) if i not in P.F]; DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
            if len(U2) != 1 or len(DT) != 2: continue
            cnt += 1
            if cnt % 10: continue
            d = U2[0]; S = tuple(g for g in P.J if all(g in I.R[x] for x in DT)); base = base_of_picks(I, Y2)
            for k in DT:
                if not (I.v[d].get(Y2[k], 0) > P.pv[d] and I.val(k, S) > P.pv[k]): continue
                kk = [x for x in DT if x != k][0]
                Z = [Y2[k], Y2[d]] + [g for g in P.J if g not in S]
                own = {i: (I.val(k, S) if i == k else P.pv[i]) for i in range(I.n) if i != d}
                thr = [i for i in own if threatened(I, i, own[i], Z)]
                role = lambda i: 'k' if i == k else "k'" if i == kk else 'u' if i == u else ('on-path' if Y2[i] != Y[i] else 'off-path')
                if not thr: C['FULL works (Z threatens nobody)'] += 1; break
                # does some g in Z - {Y'_k} given to k' fix it?
                fixes = []
                for g in Z:
                    if g == Y2[k]: continue
                    X = [[y] for y in Y2]; X[k] = list(S); X[d] = [x for x in Z if x != g]; X[kk] = [Y2[kk], g]
                    if efx0(I, X): fixes.append('Y\'_d' if g == Y2[d] else 'junk')
                key = 'Z threatens %s' % sorted(role(i) for i in thr)
                C[key + '; k\'-takes-g fix: %s' % sorted(set(fixes))] += 1
                break
    return C
tasks = []
d0 = json.load(gzip.open(SP + 'two_move_starts_n5_partial6.json.gz'))
for hg in d0['hypergraphs']:
    groups = collections.defaultdict(list)
    for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)
    chunk = []
    for g in groups.values():
        chunk += g
        if len(chunk) >= 2000: tasks.append((hg['sets'], chunk)); chunk = []
    if chunk: tasks.append((hg['sets'], chunk))
T = collections.Counter()
with mp.Pool() as pool:
    for C in pool.imap_unordered(job, tasks): T.update(C)
for k in sorted(T, key=lambda k: -T[k]): print(T[k], k)
