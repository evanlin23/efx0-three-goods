"""Why an MD EFX0 allocation is not a ROUND-P witness (kgen/rounds.md §4.9), written independently of rnd.c from
Lemma RC's structure: a witness needs a set of vertex-disjoint paths of passers (agent a passes into loc(a), the
holder of its pick); agents whose pick moved but which do not pass must be path ends (they receive).
Stages: STRUCT (no path structure: e.g. two pickless agents' picks in one bundle), GAIN (structures exist but some
chain agent does not strictly gain, or a start gets nothing), ABSORB (gains fine, but two agents hold >= 2 goods
outside their bases), OK.  GAIN gaps are split by shape: an agent that keeps its own pick and also holds the pick of a
pickless agent (a hand-off whose receiver keeps its base: two rounds, release then re-add), or other.  Run on random strict cores and on the climbs' instances.
    python3 kgen/rounds/rndp_gap.py n m SEED COUNT"""
import sys, os, itertools, random, collections, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib, zclimb, verify_k4zero as VZ


def classify(V, y, X):
    n = len(V); own = {g: i for i in range(n) for g in X[i]}
    loc = [own[y[a]] for a in range(n)]
    if any(VZ.val(V, a, X[a]) < V[a][y[a]] for a in range(n)): return 'notMD'
    mv = [a for a in range(n) if loc[a] != a]
    J = [g for g in own if g not in y]
    vJr = [sum(V[a][g] for g in X[a] if g in J and V[a][g] > 0) for a in range(n)]
    nJ0 = [sum(1 for g in X[a] if g in J and V[a][g] == 0) for a in range(n)]
    best = 'STRUCT'; rank = {'STRUCT': 0, 'GAIN': 1, 'ABSORB': 2, 'OK': 3}
    for k in range(len(mv) + 1):
        for E in itertools.combinations(mv, k):
            P = [a for a in mv if a not in E]; succ = {a: loc[a] for a in P}
            if len(set(succ.values())) < len(P): continue            # two passers into one agent
            pred = {b: a for a, b in succ.items()}
            if any(e not in pred for e in E): continue                # an end must receive
            cyc = False
            for a in P:
                c, st = a, 0
                while c in succ and st <= n:
                    c = succ[c]; st += 1
                    if c == a: cyc = True; break
                if cyc: break
            if cyc: continue
            onpath = set(P) | set(pred)
            nonend = set(P)
            extra = [0] * n; out = list(nJ0)
            for e in E:   # ends (E are exactly the agents with pred and no succ)
                tk = loc[e]
                if tk in nonend and V[tk][y[e]] > 0: extra[tk] += V[tk][y[e]]
                else: out[tk] += 1
            okg = True
            for b in onpath:
                l = (V[b][y[pred[b]]] if b in pred else 0) + vJr[b] + extra[b]
                if b not in pred and vJr[b] + extra[b] == 0: okg = False
                if not l > V[b][y[b]]: okg = False
            st = 'GAIN' if not okg else ('OK' if sum(1 for a in range(n) if out[a] >= 2) <= 1 else 'ABSORB')
            if rank[st] > rank[best]: best = st
            if best == 'OK': return best
    return best


if __name__ == '__main__':
    n, m, seed, cnt = map(int, sys.argv[1:5]); rng = random.Random(seed)
    C = collections.Counter(); ex = {}
    for t in range(cnt):
        Z = zclimb.rand_core(n, m, rng)
        res, _ = rndlib.oc1z(Z); alls, _c = rndlib.list_efx(Z)
        for r in res:
            if not r['perfect']: continue
            y = r['picks']; got = collections.Counter()
            for o in alls:
                X = [[g for g in range(m) if o[g] == i] for i in range(n)]
                c = classify(Z, y, X)
                if c != 'notMD': got[c] += 1
            C['starts'] += 1
            if r['RNDPZ'] > r['RNDOZ']: C['starts where cross-chain takes add witnesses'] += 1
            if r['RNDPZ'] > 0 and r['RNDOZ'] == 0: C['STARTS NEEDING A CROSS-CHAIN TAKE'] += 1
            for k, v in got.items(): C['alloc ' + k] += v
            if got['OK'] != r['RNDPZ']: C['COUNT MISMATCH with rnd.c'] += 1; print('MISMATCH', json.dumps(Z), r['order'], dict(got), r['RNDPZ'])
            if got['OK'] == 0: C['START WITHOUT WITNESS'] += 1
            for o in alls:   # shape of the GAIN gaps: some agent keeps its own pick and holds a pickless agent's pick
                X = [[g for g in range(m) if o[g] == i] for i in range(n)]
                if classify(Z, y, X) != 'GAIN': continue
                own = {g: i for i in range(n) for g in X[i]}; loc = [own[y[a]] for a in range(n)]
                pickless = [a for a in range(n) if not any(own[y[c]] == a for c in range(n))]
                keepadd = any(loc[b] == b and any(loc[c] == b for c in pickless) for b in range(n))
                C['GAIN of shape keep + a pickless agent\'s pick' if keepadd else 'GAIN of OTHER shape'] += 1
            for k in got:
                if k != 'OK' and k not in ex: ex[k] = (Z, r['order'])
    print(dict(C))
    for k, v in ex.items(): print('example', k, json.dumps(v[0]), 'order', v[1])
