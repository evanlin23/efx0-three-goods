"""Extremal forms of OC1^{exists max}: does every (or some) maximum-matching SD pick vector that is OPTIMAL for an
ordinal rank potential satisfy OC1?  Coordinator's test on the complete n = 4 export
(results/k4_oc1max/two_move_starts_n4.json.gz: every OC1^max-failing (type, picks) pair; a profile not in the export
has no failing maximum-matching start, so every rule holds there).

rank_i(Y) = 1 + #{g in R_i : v_i(g) > v_i(Y_i)}  (strict values, so ranks are distinct; no pick -> rank 5).
Potentials over the maximum-matching SD pick vectors of a profile (all n! orders):
  RM   rank-maximal: lexicographically maximize (#rank 1, #rank 2, #rank 3, #rank 4);
  LMR  leximin on ranks: lexicographically minimize the ranks sorted from worst to best;
  RS   minimum rank sum;
  TOP  maximum number of agents holding their top good.
For each potential: profiles where ALL optimal vectors satisfy OC1 ('all'), where SOME does ('some').
Also, for every failing vector Y and every receiver u: is some u-first maximum-matching vector RM-better than Y?
    python3 k4/sdc/extremal_rank_check.py [STRIDE]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu

RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results')


def ranks(I, p):
    out = []
    for i in range(I.n):
        if p[i] is None: out.append(5); continue
        out.append(1 + sum(1 for g in I.R[i] if I.v[i][g] > I.v[i][p[i]]))
    return tuple(out)


POT = {
    'RM': lambda r: tuple(sum(1 for x in r if x == k) for k in (1, 2, 3, 4)),
    'LMR': lambda r: tuple(-x for x in sorted(r, reverse=True)),
    'RS': lambda r: -sum(r),
    'TOP': lambda r: sum(1 for x in r if x == 1),
}


def job(a):
    sets, vals = a
    I = Inst(sets, vals); n = I.n; N = nu(I)
    vec = {}
    for order in itertools.permutations(range(n)):
        p = I.sd(order)
        if p in vec: vec[p].append(order); continue
        vec[p] = [order]
    mm = [p for p in vec if sum(x is not None for x in p) == N]
    ok = {p: I.check(p) != 'OC1 fails' for p in mm}
    C = collections.Counter(); ex = []
    C['profiles'] += 1; C['max-matching vectors'] += len(mm); C['failing max-matching vectors'] += sum(not ok[p] for p in mm)
    if all(ok.values()): C['profiles with no failing vector (export stale?)'] += 1
    rk = {p: ranks(I, p) for p in mm}
    for name, f in POT.items():
        best = max(f(rk[p]) for p in mm); O = [p for p in mm if f(rk[p]) == best]
        a_ = all(ok[p] for p in O); s_ = any(ok[p] for p in O)
        C[name + ' all optimal OK'] += a_; C[name + ' some optimal OK'] += s_
        if not a_ and len(ex) < 2: ex.append((name, [(p, rk[p], ok[p]) for p in O]))
    # receiver-first vs RM
    rm = POT['RM']
    for p in mm:
        if ok[p]: continue
        rec = [u for u in range(n) if p[u] is not None and all(I.v[i].get(p[u], 0) <= I.v[i].get(p[i], 0) for i in range(n) if i != u)]
        for u in rec:
            fu = [q for q in mm if any(o[0] == u for o in vec[q])]
            better = [q for q in fu if rm(rk[q]) > rm(rk[p])]
            C['failing (Y,u) pairs'] += 1
            C['  some u-first max vector RM-better'] += bool(better)
            C['  every u-first max vector RM-better'] += bool(fu) and len(better) == len(fu)
    return C, (sets, vals, ex) if ex else None


if __name__ == '__main__':
    STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/sdc/extremal_rank_check.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(os.path.join(RES, 'k4_oc1max', 'two_move_starts_n4.json.gz')))
    prof = {}
    for h in d['hypergraphs']:
        for st in h['starts']:
            prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    tasks = list(prof.values())[::STRIDE]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    with mp.Pool() as pool:
        for C, bad in pool.imap_unordered(job, tasks, chunksize=16):
            T.update(C)
            if bad:
                for name, O in bad[2]:
                    if shown[name] < 2:
                        shown[name] += 1
                        print('FAIL', name, json.dumps({'sets': bad[0], 'vals': bad[1], 'optimal': O}), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
