"""The S^c completions after DEMOTE-2's first step (Lemma RF-B′, k4/oc1_hall.md §24.11): at every DEMOTE-2 RF start
(one receiver d, D_T' = {k, k'}, S = the junk both value) and every k whose chain "k takes S, d takes Y'_k" is official,
every S^c-shaped completion of the post-chain state B' is enumerated (owner o takes the rest; agents with at most one
base good take at most one free good; k, holding S, takes nothing unless it owns; raw EFX0), and classified by
  - the owner's role (d, k, k', u = the old receiver, or another agent);
  - the agents taking a single free good and the good (Y'_d, or a junk good), by role, and whether the taker is frozen
    at B' (a compensated frozen slot of Lemma M^c).
Data: the n = 4 export (all 43,520 B starts) and every STEP-th DEMOTE-2 start of the n = 5 exports.

    python3 k4/oc1_hall/rf_bprime.py N5_EXPORT [N5_EXPORT ...] [--step=STEP]
"""
import sys, os, json, gzip, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened, base_of_picks, bundles_of, efx0, frozen_set
from greedy_rules import apply_chain
import _paths


def sc_all(I, base):
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]; out = []
    for o in range(I.n):
        others = [i for i in range(I.n) if i != o and len(B[i]) <= 1]
        for r in range(0, min(len(J), len(others)) + 1):
            for K in itertools.combinations(J, r):
                L = [g for g in J if g not in K]
                for who in itertools.permutations(others, r):
                    X = [list(b) for b in B]
                    for g, a in zip(K, who): X[a].append(g)
                    X[o] += L
                    if efx0(I, X): out.append((o, dict(zip(who, K)), tuple(L)))
    return out


def analyse(I, Y, u, Y2, C, tag):
    P = Picks(I, Y2)
    U2 = [i for i in range(I.n) if i not in P.F]; DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
    if len(U2) != 1 or len(DT) != 2: return
    d = U2[0]; S = tuple(g for g in P.J if all(g in I.R[x] for x in DT)); base = base_of_picks(I, Y2)
    shapes = set(); nchains = 0; full = False; frozen_used = set()
    for k in DT:
        if not (I.v[d].get(Y2[k], 0) > P.pv[d] and I.val(k, S) > P.pv[k]): continue
        nchains += 1
        kk = [x for x in DT if x != k][0]
        b2 = apply_chain(I, P, base, (k, d), S); F2 = set(frozen_set(I, b2))
        role = lambda i: 'd' if i == d else 'k' if i == k else "k'" if i == kk else 'u' if i == u else 'other'
        C[tag + 'per chain: k\' unfrozen after the chain: %s' % (kk not in F2)] += 1
        for o, sg, L in sc_all(I, b2):
            sh = tuple(sorted('%s%s<-%s' % (role(a), '(frozen)' if a in F2 else '', "Y'_d" if g == Y2[d] else 'junk') for a, g in sg.items()))
            shapes.add((role(o), sh)); frozen_used.add(any(a in F2 for a in sg))
            full = full or (o == d and not sg)
    C[tag + 'DEMOTE-2 starts'] += 1
    C[tag + 'official chains k -> d at the start: %d' % nchains] += 1
    if not nchains: return
    C[tag + 'some official chain leaves an S^c completion: %s' % bool(shapes)] += 1
    if shapes:
        best = min(shapes, key=lambda x: (len(x[1]), x[0] != 'd', x[0]))
        C[tag + 'simplest S^c shape over the chains: owner %s, singles %s' % best] += 1
        C[tag + 'FULL (owner d, no singles) for some chain: %s' % full] += 1
        C[tag + 'S^c without a frozen slot for some chain: %s' % (False in frozen_used)] += 1


def job(task):
    sets, starts, tag, step = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); seen = set(); cnt = 0
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]
        for o in st['orders']:
            Y2 = picks(I, [u] + [x for x in o if x != u])
            if None in Y2 or (json.dumps(vals), Y2) in seen: continue
            seen.add((json.dumps(vals), Y2))
            P = Picks(I, Y2)
            if len([i for i in range(I.n) if i not in P.F]) != 1: continue
            if len([k for k in P.D if threatened(I, k, P.pv[k], P.J)]) != 2: continue
            cnt += 1
            if cnt % step: continue
            analyse(I, Y, u, Y2, C, tag)
    return C


def tasks_of(path, tag, step):
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        groups = collections.defaultdict(list)
        for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)
        chunk = []
        for g in groups.values():
            chunk += g
            if len(chunk) >= 2000: yield (hg['sets'], chunk, tag, step); chunk = []
        if chunk: yield (hg['sets'], chunk, tag, step)


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    step = int(([a.split('=')[1] for a in sys.argv[1:] if a.startswith('--step=')] or ['10'])[0])
    print('$ python3 k4/oc1_hall/rf_bprime.py', *[os.path.basename(a) for a in args], '--step=%d' % step, flush=True)
    tasks = list(tasks_of(os.path.join(_paths.ROOT, 'results', 'k4_oc1max', 'two_move_starts_n4.json.gz'), 'n=4 ', 1))
    for a in args: tasks += list(tasks_of(a, 'n=5 (every %d-th) ' % step, step))
    T = collections.Counter()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, tasks): T.update(C)
    for k in sorted(T): print(k, T[k])
