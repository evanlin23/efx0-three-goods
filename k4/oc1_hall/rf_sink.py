"""The SINK form (joint conjecture with girth, k4/girth.md §7; k4/oc1_hall.md §24.11) on ALL DEMOTE-2 RF starts of the
n = 5 exports (one receiver d, |D_T'| = 2).

SINK: Y', or the state after one DEMOTE move, has an EFX0 completion in which all remaining free goods go to one agent
a in {w, d} (w = the holder of u's top good at Y, the RF path's x1), except at most one good to one other agent.
Moves tried, in this order (S = the junk valued by both truly dangerous agents):
  none  at Y';
  (C)   "k takes H0, d takes Y'_k", k in D_T', H0 an improving subset of S, d wanting Y'_k;
  (C')  a canonical chain from k in D_T' with H0 an improving subset of S, head h != d (or longer chains).
Completions: raw EFX0 (ohlib.efx0), every assignment of the free goods of that form.

    python3 k4/oc1_hall/rf_sink.py N5_EXPORT [N5_EXPORT ...]
"""
import sys, os, json, gzip, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, threatened, base_of_picks, bundles_of, efx0
from greedy_rules import apply_chain, canonical_paths
import _paths


def sink_ok(I, base, owners):
    B = bundles_of(I, base); J = [g for g in range(I.m) if base[g] < 0]
    for a in owners:
        cands = [None] + [i for i in range(I.n) if i != a]
        for s in cands:
            for g in ([None] if s is None else J):
                X = [list(b) for b in B]
                if s is not None: X[s].append(g)
                X[a] += [h for h in J if h != g]
                if efx0(I, X): return True
    return False


def job(task):
    sets, starts = task
    m = 1 + max(max(s) for s in sets); C = collections.Counter(); seen = set(); bad = []
    for st in starts:
        vals = st['vals']; I = Inst(sets, vals, m); Y = tuple(st['picks']); u = st['receivers'][0]
        for o in st['orders']:
            Y2 = picks(I, [u] + [x for x in o if x != u])
            if None in Y2 or (json.dumps(vals), Y2) in seen: continue
            seen.add((json.dumps(vals), Y2)); P = Picks(I, Y2)
            U2 = [i for i in range(I.n) if i not in P.F]; DT = [k for k in P.D if threatened(I, k, P.pv[k], P.J)]
            if len(U2) != 1 or len(DT) != 2: continue
            d = U2[0]; w = [i for i in range(I.n) if Y[i] == Y2[u]][0]
            owners = sorted({w, d})
            C['DEMOTE-2 starts'] += 1
            base = base_of_picks(I, Y2)
            if sink_ok(I, base, owners): C['SINK at Y\''] += 1; continue
            S = [g for g in P.J if all(g in I.R[k] for k in DT)]
            done = None
            for k in DT:
                subs = sorted([H for r in range(1, len(S) + 1) for H in itertools.combinations(S, r) if I.val(k, H) > P.pv[k]], key=len)
                if I.v[d].get(Y2[k], 0) > P.pv[d]:
                    for H in subs:
                        if sink_ok(I, apply_chain(I, P, base, (k, d), H), owners): done = '(C) k -> d'; break
                if done: break
            if not done:
                for k in DT:
                    subs = sorted([H for r in range(1, len(S) + 1) for H in itertools.combinations(S, r) if I.val(k, H) > P.pv[k]], key=len)
                    for path in canonical_paths(I, P, k):
                        if path == (k, d): continue
                        for H in subs:
                            if sink_ok(I, apply_chain(I, P, base, path, H), owners): done = "(C') head %s, length %d" % ('d' if path[-1] == d else 'frozen', len(path) - 1); break
                        if done: break
                    if done: break
            C['SINK after %s' % done if done else 'SINK FAILS'] += 1
            if not done and len(bad) < 3: bad.append({'sets': sets, 'vals': vals, 'Y': list(Y), "Y'": list(Y2), 'u': u, 'w': w, 'd': d, 'DT': DT})
    return C, bad


def tasks_of(path):
    d = json.load(gzip.open(path))
    for hg in d['hypergraphs']:
        groups = collections.defaultdict(list)
        for st in hg['starts']: groups[json.dumps(st['vals'])].append(st)
        chunk = []
        for g in groups.values():
            chunk += g
            if len(chunk) >= 2000: yield (hg['sets'], chunk); chunk = []
        if chunk: yield (hg['sets'], chunk)


if __name__ == '__main__':
    print('$ python3 k4/oc1_hall/rf_sink.py', *[os.path.basename(p) for p in sys.argv[1:]], flush=True)
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(job, [t for p in sys.argv[1:] for t in tasks_of(p)]):
            T.update(C)
            for b in bad:
                if shown < 6: shown += 1; print('SINK FAILS:', json.dumps(b), flush=True)
    for k in sorted(T): print(k, T[k])
