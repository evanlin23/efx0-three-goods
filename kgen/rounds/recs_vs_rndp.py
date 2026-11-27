"""Is REC-S's first chain E(k) one of ROUND-P's chains?  (coordinator, burst 5 item 3; REC-S = Theorem REC-S of
k4/oc1max_multi.md §12 on proof/k4-oc1max-multi.)  Input: the multi session's REC-S witnesses, one per n = 4 start
with no one-move repair (results/k4_oc1max_multi/recs_witnesses_n4.json.gz on proof/k4-oc1max-multi; read with
`git show origin/proof/k4-oc1max-multi:results/k4_oc1max_multi/recs_witnesses_n4.json.gz > FILE`).
For every start, every MD EFX0 allocation (rnd.c list_efx) and every Lemma RC path structure that witnesses the round
(written here, as in rndp_gap.classify):
  RNDOZ  a round of OC1' moves (non-end agents take only their own chain end's goods),
  RNDPZ  ROUND-P (any chain end's goods).
Reported per start, with P1 = the witness's E(k), and E(k) recomputed for every dangerous k (frozen: some agent wants
its pick; values a junk good; as in check_recs.py):
  P1 exact        P1 is a chain (path with t >= 1, same agent sequence) of some witness round,
  P1 prefix       some witness chain starts with P1 (P1 extended),
  some E(k) exact some dangerous k's E(k) is a chain of some witness round,
  X_RECS round    REC-S's own final allocation X is a witness (the two sequential moves compose into one round),
                  and how E(k) and P2 appear in its round structures.
    python3 kgen/rounds/recs_vs_rndp.py FILE [STRIDE] [JOBS]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import rndlib


def structures(V, y, X, pooled):
    """the chains (agent tuples, t >= 1) of every path structure that witnesses the round at X (raw: MD, gains,
    one absorber)"""
    n = len(V); own = {g: i for i in range(n) for g in X[i]}
    loc = [own[y[a]] for a in range(n)]
    if any(sum(V[a][g] for g in X[a]) < V[a][y[a]] for a in range(n)): return None
    mv = [a for a in range(n) if loc[a] != a]; picks = set(y)
    vJr = [sum(V[a][g] for g in X[a] if g not in picks and V[a][g] > 0) for a in range(n)]
    nJ0 = [sum(1 for g in X[a] if g not in picks and V[a][g] == 0) for a in range(n)]
    found = []
    for k in range(len(mv) + 1):
        for E in itertools.combinations(mv, k):
            P = [a for a in mv if a not in E]; succ = {a: loc[a] for a in P}
            if len(set(succ.values())) < len(P): continue
            pred = {b: a for a, b in succ.items()}
            if any(e not in pred for e in E): continue
            starts = [a for a in P if a not in pred]; chains = []; seen = set()
            for a in starts:
                c = [a]
                while c[-1] in succ: c.append(succ[c[-1]])
                chains.append(tuple(c)); seen |= set(c)
            if seen != set(P) | set(pred): continue            # a cycle of passers: not a round
            chain_of = {a: ch for ch in chains for a in ch}
            ends = [ch[-1] for ch in chains]
            extra = [0] * n; out = list(nJ0)
            for e in ends:
                tk = loc[e]
                ok_take = tk in chain_of and tk != chain_of[tk][-1] and V[tk][y[e]] > 0 and (pooled or chain_of[tk] == chain_of[e])
                if loc[e] == e: out[e] += 1                     # an end holding its own pick: it stays outside
                elif ok_take: extra[tk] += V[tk][y[e]]
                else: out[tk] += 1
            okg = True
            for ch in chains:
                for i, b in enumerate(ch):
                    l = (V[b][y[ch[i - 1]]] if i > 0 else 0) + vJr[b] + extra[b]
                    if i == 0 and vJr[b] + extra[b] == 0: okg = False
                    if not l > V[b][y[b]]: okg = False
            if okg and sum(1 for a in range(n) if out[a] >= 2) <= 1: found.append(tuple(chains))
    return found


def ek_chains(V, y, order):
    n = len(V); J = [g for g in range(len(V[0])) if g not in set(y)]
    p = [V[i][y[i]] for i in range(n)]; pos = {a: t for t, a in enumerate(order)}
    wants = lambda i, g: V[i][g] > p[i]
    out = {}
    for k in range(n):
        if not any(wants(i, y[k]) for i in range(n) if i != k) or not any(V[k][g] > 0 for g in J): continue
        P = [k]
        while True:
            ws = [i for i in range(n) if i != P[-1] and wants(i, y[P[-1]])]
            if not ws: break
            P.append(min(ws, key=lambda i: pos[i]))
        out[k] = tuple(P)
    return out


def job(st):
    sets, vals, y, w = st['sets'], st['vals'], tuple(st['picks']), st['witness']
    m = 1 + max(max(s) for s in sets); n = len(sets); V = [[0] * m for _ in sets]
    for i, (s, vv) in enumerate(zip(sets, vals)):
        for g, x in zip(s, vv): V[i][g] = x
    alls, _ = rndlib.list_efx(V)
    P1 = tuple(w['P1']); EK = ek_chains(V, y, w['order']); res = {}
    Xr = [sorted(b) for b in w['X']]
    for mode, pooled in (('RNDOZ', False), ('RNDPZ', True)):
        chains = set(); cnt = 0
        for o in alls:
            X = [[g for g in range(m) if o[g] == i] for i in range(n)]
            f = structures(V, y, X, pooled)
            if f:
                cnt += 1
                for cs in f: chains |= set(cs)
        res[mode] = {'witnesses': cnt, 'P1 exact': P1 in chains, 'P1 prefix': any(c[:len(P1)] == P1 for c in chains),
                     'some E(k) exact': any(e in chains for e in EK.values()),
                     'X_RECS round': bool(structures(V, y, Xr, pooled)),
                     'X_RECS chains': [list(map(list, cs)) for cs in (structures(V, y, Xr, pooled) or [])][:2],
                     'X_RECS chains_all': structures(V, y, Xr, pooled) or []}
    return st['list'], st['idx'], list(y), w, EK, res


if __name__ == '__main__':
    fn = sys.argv[1]; STRIDE = int(sys.argv[2]) if len(sys.argv) > 2 else 1; JOBS = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    print('$ python3 kgen/rounds/recs_vs_rndp.py', *sys.argv[1:], flush=True)
    S = json.load(gzip.open(fn))['starts'][::STRIDE]; t0 = time.time()
    C = collections.Counter(); ex = collections.defaultdict(list)
    with mp.Pool(JOBS) as pool:
        for t, (L, idx, y, w, EK, res) in enumerate(pool.imap_unordered(job, S, chunksize=64)):
            C['starts'] += 1
            for mode, r in res.items():
                if r['witnesses'] == 0: C[(mode, 'NO WITNESS')] += 1
                for key in ('P1 exact', 'P1 prefix', 'some E(k) exact', 'X_RECS round'):
                    C[(mode, key, r[key])] += 1
                    if not r[key] and len(ex[(mode, key)]) < 3:
                        ex[(mode, key)].append({'list': L, 'idx': idx, 'picks': y, 'witness': w, 'Ek': {str(k): v for k, v in EK.items()},
                                                'X_RECS chains': r['X_RECS chains']})
                if r['X_RECS round']:   # how E(k) and P2 combine in the one-round structures of REC-S's allocation
                    P1, P2 = tuple(w['P1']), tuple(w['P2']); sig = set()
                    for cs in r['X_RECS chains_all']:
                        if len(cs) == 1 and set(cs[0]) == set(P1) | set(P2): sig.add('one chain on the agents of E(k) and P2')
                        elif len(cs) == 1: sig.add('one chain, other agents')
                        elif P1 in cs or P2 in cs: sig.add('several chains, E(k) or P2 among them')
                        else: sig.add('several chains')
                    for x in sig: C[(mode, 'X_RECS structure', x)] += 1
                    if sig == {'one chain on the agents of E(k) and P2'}: C[(mode, 'X_RECS: only a single spliced chain')] += 1
                if r['X_RECS round'] and len(ex[(mode, 'X_RECS round chains')]) < 3:
                    ex[(mode, 'X_RECS round chains')].append({'list': L, 'idx': idx, 'P1': w['P1'], 'P2': w['P2'], 'chains': r['X_RECS chains']})
            if (t + 1) % 10000 == 0: print('...', t + 1, '%.0fs' % (time.time() - t0), flush=True)
    for k in sorted(C, key=str): print(k, C[k])
    for k, v in ex.items():
        for e in v: print('example', k, json.dumps(e))
    print('time %.0f s' % (time.time() - t0))
