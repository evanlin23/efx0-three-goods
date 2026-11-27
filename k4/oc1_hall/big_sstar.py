"""OC1 in the shape S* at larger n (k4/oc1_hall.md §7), by SAT.  S* completion: complete EFX0 (sdclib's encoding),
bases kept, at most one agent (the owner) receives two or more junk goods, and an agent that is not a holder (a
frozen agent or a multi-good holder) receives junk only if it is the owner.  For sampled orders of random instances:
picks complete in S*, or some improving chain (k4/sdc/de_free.iter_chains with junk sets of at most DF_HMAX goods,
chains of at most DF_TMAX + 1 agents) gives an S* completion; first the chains from dangerous agents with owner x_0
(Finding B), then any chain with any owner.

    python3 k4/oc1_hall/big_sstar.py cores:FILE N SEED ORDERS | big:N COUNT SEED ORDERS
"""
import sys, os, json, gzip, random, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ohlib import Inst, picks, Picks, base_of_picks, bundles_of, frozen_set
from sdclib import Enc
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
import de_free as DF
import _paths


def sstar_sat(E, I, base, owner=None):
    """S* completion by SAT; owner None = any agent may be the owner"""
    B = bundles_of(I, base); F = set(frozen_set(I, base))
    holders = set(j for j in range(I.n) if len(B[j]) <= 1 and j not in F)
    J = [g for g in range(I.m) if base[g] < 0]
    cl = list(E.cl); top = E.top
    for g in range(I.m):
        cl.append([-E.x[g][I.n]])
        if base[g] >= 0: cl.append([E.x[g][base[g]]])
    bigs = []
    for i in range(I.n):
        top += 1; b = top; bigs.append(b)
        for g, h in itertools.combinations(J, 2): cl.append([-E.x[g][i], -E.x[h][i], b])
        if i not in holders:
            for g in J: cl.append([-E.x[g][i], b])
        if owner is not None and i != owner: cl.append([-b])
    enc = CardEnc.atmost(lits=bigs, bound=1, top_id=top, encoding=EncType.seqcounter)
    cl.extend(enc.clauses)
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


def instances(spec, rng):
    kind, rest = spec.split(':', 1)
    os.chdir(_paths.DE4)
    from de4lib import random_profile
    os.chdir(_paths.ROOT)
    out = []
    if kind == 'cores':
        fn, N = rest, int(sys.argv[2])
        cores = [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); out.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        n, N = int(rest), int(sys.argv[2])
        for t in range(N):
            m = rng.randint(n + 2, 2 * n)
            while True:
                sets = [sorted(rng.sample(range(m), rng.choice([3, 4, 4]))) for _ in range(n)]
                if len(set().union(*map(set, sets))) == m: break
            out.append(('b%d' % t, sets, random_profile(sets, rng), m))
    return out


if __name__ == '__main__':
    spec = sys.argv[1]; seed = int(sys.argv[3]); NORD = int(sys.argv[4]); rng = random.Random(seed)
    C = collections.Counter(); t0 = time.time()
    print('$ python3 k4/oc1_hall/big_sstar.py', *sys.argv[1:], 'DF_HMAX=%d DF_TMAX=%d' % (DF.HMAX, DF.TMAX), flush=True)
    for name, sets, vals, m in instances(spec, rng):
        I = Inst(sets, vals, m, name); E = Enc(sets, vals, m); n = I.n; seen = set()
        C['instances'] += 1
        for _ in range(NORD):
            od = rng.sample(range(n), n); Y = picks(I, od)
            if Y in seen: continue
            seen.add(Y); C['distinct starts'] += 1
            base = base_of_picks(I, Y)
            if sstar_sat(E, I, base): C['picks complete in S*'] += 1; continue
            P = Picks(I, Y); C['hard starts'] += 1
            ok = None
            for b2 in DF.iter_chains(E, base):
                B2 = bundles_of(I, b2)
                # x_0 = the agent whose base changed but did not receive an old base of someone ... use: owner = each D agent whose base changed
                cand = [k for k in P.D if sorted(B2[k]) != sorted(P.Y[k:k + 1]) and P.Y[k] not in B2[k]]
                if any(sstar_sat(E, I, b2, owner=k) for k in cand): ok = 'D agent owns'; break
            if ok is None:
                for b2 in DF.iter_chains(E, base):
                    if sstar_sat(E, I, b2): ok = 'any'; break
            C['hard start repaired: %s' % ok] += 1
            if ok is None:
                print('NOT REPAIRED', name, json.dumps((sets, vals)), 'order', od, 'picks', Y, flush=True)
        if C['instances'] % 20 == 0:
            print('...', dict(C), '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
