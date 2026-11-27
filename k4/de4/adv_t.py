"""Adversarial search (EVIDENCE; ledger K4.DE4V3R.T) for a counterexample to Claim T / the robust candidate around GM4-B's double clash: two
lower-pair holders, frozen holders of their tops whose b is a leftover good, holders of their b's (6 agents), plus
NEXTRA extra goods valued by several agents. For each instance: Phi*,
every (V3)-valid state of Phi* that is not all-upper: completable? Also every maximum: completable?

    python3 k4/de4/adv_t.py PER JOBS SEED NEXTRA     (logs results/k4_de4/adv_t_NEXTRA.log)"""
import sys, os, json, random, collections, multiprocessing as mp, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import claimd as CD
CT = CD.CT; T = CD.T; S = CD.S
from de4lib import Inst, wanted_goods, leftover
from dead import strict_ok
def make(rng, nextra):
    a_u, a_v, b_u, b_v, c_u, d_u, c_v, d_v, j = range(9)
    ex = list(range(9, 9 + nextra))
    base = [b_u, b_v, c_u, d_u, c_v, d_v, a_u, a_v] + ex
    cx = rng.choice([c_u, d_u]); cxp = rng.choice([c_v, d_v])
    def fill(s, pool, k):
        s = set(s)
        while len(s) < k: s.add(rng.choice(pool))
        return sorted(s)
    sets = [[a_u, b_u, c_u, d_u], [a_v, b_v, c_v, d_v],
            fill({a_v, j, cx}, [g for g in base if g != a_v], rng.choice([3, 4])),
            fill({a_u, j, cxp}, [g for g in base if g != a_u], rng.choice([3, 4])),
            fill({b_u}, [g for g in base + [j] if g != b_u], rng.choice([3, 4])),
            fill({b_v}, [g for g in base + [j] if g != b_v], rng.choice([3, 4]))]
    for g in ex:
        if not any(g in s for s in sets): return None
    I = None
    vals = []
    for i, s in enumerate(sets):
        for _ in range(3000):
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
                ok = r[0] == (b_u if i == 4 else b_v)
            if ok: break
        else:
            return None
        vals.append(V)
    I = Inst(sets, vals, 9 + nextra)
    return I if strict_ok(I) else None
def job(args):
    per, seed, nextra = args
    rng = random.Random(seed); C = collections.Counter(); ex = []
    for _ in range(per):
        I = make(rng, nextra)
        if I is None: continue
        All, ph, P = CT.states(I)
        if not All: continue
        C['instances'] += 1
        Cm = S.Comp(I)
        top = [Y for Y, p in zip(All, ph) if p == P and T.v3ok(I, Y)]
        V = [CT.vals(I, Y) for Y in top]
        for k, Y in enumerate(top):
            mx = not any(all(a >= b for a, b in zip(V[l], V[k])) and V[l] != V[k] for l in range(len(top)))
            allup = all(T.isupper(I, i, Y[i]) for i in range(I.n))
            comp = Cm.ok([list(A) for A in Y])
            if not comp:
                C['NON-COMPLETABLE top state: all-upper %s, maximum %s' % (allup, mx)] += 1
                if not allup or mx: ex.append((I.sets, [I.v[i] for i in range(I.n)], [list(A) for A in Y], allup, mx))
            else:
                C['top states completable'] += 1
    return C, ex
if __name__ == '__main__':
    per, jobs, seed, nextra = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    tot, EX = collections.Counter(), []
    t0 = time.time()
    with mp.Pool(3) as p:
        for C, ex in p.imap_unordered(job, [(per, seed + k, nextra) for k in range(jobs)]): tot.update(C); EX += ex
    for k in sorted(tot): print('%7d  %s' % (tot[k], k))
    for e in EX[:5]: print('EX', json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
