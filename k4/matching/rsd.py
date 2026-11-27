"""Iterated reduction (RSD, the coordinator's question; k4/matching.md §6): does settling sharers one at a time, with
no other move, repair every start with no one-move repair?

One reduction step at a state B of the current instance I' (a perfect SD start of it) is:
  - a canonical chain P from an agent k that is dangerous in I' (each later agent takes its predecessor's single
    good, and gains);
  - k takes a pair T inside (J' + B_end) with v_k(T) > v_k(B_k);
  - Lemma LIFT's hypothesis in I': every other agent of I' values each good of T below its value after P.  With
    TSIZE=any, T is any improving subset of (J' + B_end) instead, provided it threatens no other agent of I' at its
    value after P.  For a pair this is the same condition, up to ties.  With LSTAR=defer, (L*) is not required at
    the step at all.  Only the final allocation's raw EFX0 test in I applies, so a deleted T may threaten an agent
    until a later step raises that agent's value.
  - the reduced state (k and T deleted) is again a perfect SD outcome of the smaller instance I'' (checked over all
    orders). With MODE=E, P must instead be the earliest-wanter chain E(k) of a tracked order, and the reduced
    state's order is that order minus k (Lemma SD-E, multi session).
RSD(d) holds at a start when at most d reduction steps reach a state whose one-absorber completion lifts. Lifting
means:
  - every deleted agent keeps its T and receives nothing;
  - the owner is a present agent;
  - the whole allocation is raw EFX0 in the original instance.
This is the coordinator's "lift every level" with the phantom constraints checked exactly. RSD+(d) also allows one
official move of the last instance (k4/sdc Inst.moves) before the completion. RSD+(1) is OC2-REC without the
"shared" condition.

For each start the script records the least d with RSD(d), the least d with RSD+(d), and whether every T in the
successful sequence is shared, i.e. improving for a second agent dangerous at that level.  With EXPLORE=1 it also
walks every sequence of reduction steps.  It counts the starts from which some dead end is reachable: a state with
no lifting completion and no reduction step.  If none is, any greedy choice of steps repairs.

    [MODE=canon|E] [TSIZE=2|any] [DMAX=4] python3 k4/matching/rsd.py INPUT [INPUT ...]     (inputs as in n5_census.py)"""
import sys, os, json, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from n5_census import load

MODE = os.environ.get('MODE', 'canon'); DMAX = int(os.environ.get('DMAX', '4'))
TSIZE = os.environ.get('TSIZE', '2')   # '2': pairs T (Lemma LIFT); 'any': any improving T that threatens nobody
LSTAR = os.environ.get('LSTAR', 'now')  # 'now': (L*) at the step; 'defer': no (L*) at the step, only the final raw check


def sub_instance(I, alive, goods):
    g2 = {g: t for t, g in enumerate(goods)}
    sets = [[g2[g] for g in I.sets[i] if g in g2] for i in alive]
    vals = [[I.v[i][g] for g in I.sets[i] if g in g2] for i in alive]
    return M(sets, vals, m=len(goods)), g2


DEADRECV = os.environ.get('DEADRECV') == '1'   # the final completion may also hand junk to deleted agents


def lifted_completion(I, B, dead):
    """B: full state of I (dead agents hold their T); a one-absorber completion with a present owner, dead agents
    receiving nothing, raw EFX0 in I.  Brute force.  With DEADRECV=1 deleted agents are ordinary agents of the
    completion (any of them may own, or receive one good)."""
    used = set(g for b in B for g in b); J = [g for g in range(I.m) if g not in used]
    alive = [i for i in range(I.n) if i not in dead] if not DEADRECV else list(range(I.n))
    for o in alive:
        recv = [u for u in alive if u != o]
        for lab in itertools.product([o] + recv, repeat=len(J)):
            if any(lab.count(u) > 1 for u in recv): continue
            X = [list(b) for b in B]
            for g, u in zip(J, lab): X[u].append(g)
            if I.efx0(X): return X
    return None


def earliest(Im, Bm, k, order):
    pos = {a: t for t, a in enumerate(order)}; P = [k]
    while True:
        y = Bm[P[-1]][0]
        ws = [i for i in range(Im.n) if i != P[-1] and i not in P and Im.wants(i, y, Bm)]
        if not ws: return P
        P.append(min(ws, key=lambda i: pos[i]))


def steps(I, alive, goods, B, orders):
    """Reduction steps at the state B (full, of I) of the instance on alive agents / goods.  Yields
    (k, T, P, new full state, new orders, shared)."""
    Im, g2 = sub_instance(I, alive, goods); inv = {t: g for g, t in g2.items()}
    Bm = [[g2[g] for g in B[i]] for i in alive]; Jm = Im.junk(Bm); Dm = Im.dangerous(Bm)
    for km in Dm:
        if MODE == 'E':
            cands = {}
            for o in orders:
                om = [alive.index(a) for a in o]
                cands.setdefault(tuple(earliest(Im, Bm, km, om)), []).append(o)
            chains = list(cands.items())
        else:
            chains = []

            def ext(path):
                x = path[-1]
                for w in range(Im.n):
                    if w in path or not Im.wants(w, Bm[x][0], Bm): continue
                    chains.append((tuple(path + [w]), orders)); ext(path + [w])
            ext([km])
        for P, ords in chains:
            if len(P) < 2: continue
            pool = [g for g in Jm + list(Bm[P[-1]]) if g in Im.R[km]]
            sizes = [2] if TSIZE == '2' else range(1, len(pool) + 1)
            for T in (T for r in sizes for T in itertools.combinations(pool, r)):
                if Im.V(km, T) <= Im.V(km, Bm[km]): continue
                nb = [list(b) for b in Bm]; nb[km] = list(T)
                for t in range(1, len(P)): nb[P[t]] = list(Bm[P[t - 1]])
                if LSTAR == 'defer': pass
                elif TSIZE == '2':
                    if any(Im.v[i].get(g, 0) >= Im.V(i, nb[i]) for i in range(Im.n) if i != km for g in T): continue
                elif any(Im.threat(i, list(T), Im.V(i, nb[i])) for i in range(Im.n) if i != km): continue
                shared = any(q != km and Im.V(q, [g for g in T if g in Im.R[q]]) > Im.V(q, Bm[q]) for q in Dm)
                k = alive[km]; Tg = [inv[g] for g in T]
                alive2 = [a for a in alive if a != k]; goods2 = [g for g in goods if g not in Tg]
                full = [list(b) for b in B]
                for a, i in enumerate(alive): full[i] = [inv[g] for g in nb[a]]
                I2, h2 = sub_instance(I, alive2, goods2)
                Y2 = tuple(h2[full[i][0]] for i in alive2)
                if any(len(full[i]) != 1 for i in alive2): continue
                if MODE == 'E':
                    o2 = [[a for a in o if a != k] for o in ords]
                    o2 = [o for o in o2 if I2.sd([alive2.index(a) for a in o]) == Y2]
                    if not o2: continue
                else:
                    if not any(I2.sd(p) == Y2 for p in itertools.permutations(range(I2.n))): continue
                    o2 = orders
                yield k, Tg, [alive[p] for p in P], full, o2, shared


def search(I, alive, goods, B, orders, dead, d, plus):
    """Least-depth search: a list of (k, T, P, shared, state after the step) steps reaching a lifting completion,
    ending with ('X', allocation) (or ('move', state, allocation) for RSD+), or None."""
    X = lifted_completion(I, B, dead)
    if X is not None: return [('X', X)]
    if plus:
        Im, g2 = sub_instance(I, alive, goods); inv = {t: g for g, t in g2.items()}
        Bm = [[g2[g] for g in B[i]] for i in alive]
        for C in Im.moves(Bm):
            full = [list(b) for b in B]
            for a, i in enumerate(alive): full[i] = [inv[g] for g in C[a]]
            X = lifted_completion(I, full, dead)
            if X is not None: return [('move', full, X)]
    if d == 0: return None
    for k, T, P, full, o2, shared in steps(I, alive, goods, B, orders):
        alive2 = [a for a in alive if a != k]; goods2 = [g for g in goods if g not in T]
        r = search(I, alive2, goods2, full, o2, dead | {k}, d - 1, plus)
        if r is not None: return [(k, T, P, shared, full)] + r
    return None


def explore(I, alive, goods, B, orders, dead, d, memo, C):
    """Every state reachable by reduction steps (at most d more): count dead ends (no lifting completion and no
    step).  Returns True if no dead end is reachable from here."""
    key = (tuple(alive), json.dumps(B))
    if key in memo: return memo[key]
    comp = lifted_completion(I, B, dead) is not None
    nxt = list(steps(I, alive, goods, B, orders)) if d > 0 else []
    if not comp and not nxt:
        C['reachable dead-end states (no completion, no step)%s' % ('' if d > 0 else ' at the depth limit')] += 1
        memo[key] = False; return False
    ok = True
    for k, T, P, full, o2, shared in nxt:
        ok &= explore(I, [a for a in alive if a != k], [g for g in goods if g not in T], full, o2, dead | {k}, d - 1,
                      memo, C)
    memo[key] = ok; return ok


def job(row):
    I = M(row['sets'], row['vals']); B = [[g] for g in row['picks']]; C = collections.Counter(); wit = None
    orders = [list(o) for o in row.get('orders') or ([row['order']] if 'order' in row else
                                                   [o for o in itertools.permutations(range(I.n)) if I.sd(o) == tuple(row['picks'])])]
    for plus in (False, True):
        tag = 'RSD+' if plus else 'RSD'; found = None
        for d in range(DMAX + 1):
            r = search(I, list(range(I.n)), list(range(I.m)), B, orders, frozenset(), d, plus)
            if r is not None: found = (d, r); break
        if found is None:
            C['%s: none with d <= %d' % (tag, DMAX)] += 1
            sys.stdout.write('%s FAILS %s\n' % (tag, json.dumps({'sets': row['sets'], 'vals': row['vals'], 'picks': list(row['picks'])}))); sys.stdout.flush()
        else:
            d, r = found; st = [x for x in r if x[0] not in ('X', 'move')]
            C['%s: least d = %d' % (tag, d)] += 1
            C['%s: every step shared %s' % (tag, all(x[3] for x in st))] += 1
            C['%s: sizes of T along the sequence %s' % (tag, [len(x[1]) for x in st])] += 1
            assert I.efx0(r[-1][-1])
            if not plus: wit = {'k': row.get('_k'), 'steps': [{'k': x[0], 'T': x[1], 'P': x[2], 'state': x[4]} for x in st],
                                'alloc': r[-1][-1]}
    if os.environ.get('EXPLORE'):
        D = collections.Counter()
        ok = explore(I, list(range(I.n)), list(range(I.m)), B, orders, frozenset(), DMAX, {}, D)
        C['EXPLORE: no dead end reachable %s' % ok] += 1
        for k in D: C['EXPLORE: starts with ' + k] += 1
    return C, wit


if __name__ == '__main__':
    rows = []
    for a in sys.argv[1:]: rows += load(a)
    seen = set(); R = []
    for r in rows:
        key = json.dumps([r['sets'], r['vals'], list(r['picks'])])
        if key not in seen: seen.add(key); R.append(r)
    print('$ MODE=%s TSIZE=%s LSTAR=%s DMAX=%d DEADRECV=%d python3 k4/matching/rsd.py' % (MODE, TSIZE, LSTAR, DMAX, DEADRECV), *sys.argv[1:], '|', len(R), 'distinct starts', flush=True)
    for t, r in enumerate(R): r['_k'] = t
    T = collections.Counter(); t0 = time.time(); WIT = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for t, (C, wit) in enumerate(pool.imap_unordered(job, R, chunksize=4 if len(R) > 1000 else 1)):
            T.update(C)
            if wit is not None: WIT.append(wit)
            if (t + 1) % 10000 == 0: print('...', t + 1, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    if os.environ.get('RSD_WIT'):
        import gzip
        WIT.sort(key=lambda w: w['k'])
        with gzip.open(os.environ['RSD_WIT'], 'wt') as f:
            json.dump({'what': 'RSD witnesses (k4/matching/rsd.py, MODE=%s TSIZE=%s): per start k (index into the distinct input '
                               'rows, in input order), the reduction steps (deleted agent k, its set T, canonical chain P, full '
                               'state after the step) and the final allocation' % (MODE, TSIZE),
                       'inputs': sys.argv[1:], 'witnesses': WIT}, f)
        print('wrote', os.environ['RSD_WIT'], len(WIT), 'witnesses')
    print('time %.0f s' % (time.time() - t0))
