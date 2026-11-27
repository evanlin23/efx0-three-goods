"""Targeted search (EVIDENCE; ledger K4.DE4V3R.T) for a counterexample to the robust candidate (Claim T) with one leftover good: GM4-B's double clash
(lower-pair holders 0, 1; frozen holders 2, 3 of their tops whose b is the leftover good j) with the b's of 0 and 1
held in upper pairs by agents 4, 5 (so no free agent holds one good), and the frozen agents valuing those b's.
For each random instance: every (V3)-valid state of the largest level sum: completable? all-upper?

    python3 k4/de4/adv_t3.py PER JOBS SEED     (log results/k4_de4/adv_t3.log)"""
import sys, os, json, random, collections, multiprocessing as mp, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import claimd as CD
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst
from dead import strict_ok
def make(rng):
    a_u, a_v, b_u, b_v, c_u, d_u, c_v, d_v, j, e1, e2 = range(11)
    cx = rng.choice([c_u, d_u]); cxp = rng.choice([c_v, d_v])
    sets = [[a_u, b_u, c_u, d_u], [a_v, b_v, c_v, d_v],
            sorted({a_v, j, cx, rng.choice([b_u, b_v, e1, e2])}), sorted({a_u, j, cxp, rng.choice([b_v, b_u, e1, e2])}),
            sorted({b_u, e1} | set(rng.sample([a_u, a_v, c_v, d_v, j, e2], rng.choice([1, 2])))),
            sorted({b_v, e2} | set(rng.sample([a_u, a_v, c_u, d_u, j, e1], rng.choice([1, 2]))))]
    sets = [s[:4] if len(s) > 4 else s for s in sets]
    if any(len(s) < 3 for s in sets): return None
    vals = []
    for i, s in enumerate(sets):
        for _ in range(4000):
            V = rng.sample(range(1, 40), len(s))
            d = dict(zip(s, V))
            if max(V) >= sum(V) - max(V): continue
            r = sorted(s, key=lambda g: -d[g])
            if i in (0, 1):
                a, b = (a_u, b_u) if i == 0 else (a_v, b_v)
                c, dd = (c_u, d_u) if i == 0 else (c_v, d_v)
                ok = r[0] == a and r[1] == b and d[b] < d[c] + d[dd] < d[a] and d[c] > d[dd]
            elif i in (2, 3):
                ok = r[0] == (a_v if i == 2 else a_u) and r[1] == j
            else:
                bb, ee = (b_u, e1) if i == 4 else (b_v, e2)
                ok = d[bb] + d[ee] > r[0] if r[0] not in (bb, ee) else (d[bb] + d[ee] > d[r[0]] and all(d[g] <= d[r[0]] for g in (bb, ee)))
                ok = ok and d[bb] + d[ee] > max(d[g] for g in s) and max(d[bb], d[ee]) <= max(d[g] for g in s)
            if ok: break
        else:
            return None
        vals.append(V)
    I = Inst(sets, vals, 11)
    return I if strict_ok(I) else None
def job(args):
    per, seed = args
    rng = random.Random(seed); C = collections.Counter(); ex = []
    for _ in range(per):
        I = make(rng)
        if I is None: continue
        C['instances'] += 1
        Y = [[4, 5], [6, 7], [1], [0], [2, 9], [3, 10]]
        if CD.valid(I, Y) and T.v3ok(I, Y): C['  pattern state valid'] += 1
        All, ph, P = CT.states(I)
        Cm = S.Comp(I)
        top = [Y for Y, p in zip(All, ph) if p == P and T.v3ok(I, Y)]
        V = [CT.vals(I, Y) for Y in top]
        for k, Y in enumerate(top):
            if not Cm.ok([list(A) for A in Y]):
                mx = not any(all(a >= b for a, b in zip(V[l], V[k])) and V[l] != V[k] for l in range(len(top)))
                allup = all(T.isupper(I, i, Y[i]) for i in range(I.n))
                C['NON-COMPLETABLE top state: all-upper %s, maximum %s' % (allup, mx)] += 1
                ex.append((I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], allup, mx))
        C['  top states'] += len(top)
    return C, ex
if __name__ == '__main__':
    per, jobs, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    tot, EX = collections.Counter(), []
    t0 = time.time()
    with mp.Pool(2) as p:
        for C, ex in p.imap_unordered(job, [(per, seed + k) for k in range(jobs)]): tot.update(C); EX += ex
    for k in sorted(tot): print('%7d  %s' % (tot[k], k))
    for e in EX[:5]: print('EX', json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
