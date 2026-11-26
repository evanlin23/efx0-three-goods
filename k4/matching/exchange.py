"""The exchange form of an improving chain (k4/matching.md §3): Lemma EX and Conjecture CM.

Setting: a perfect start Y (every agent with a relevant good holds its pick y_i, value p_i), junk J.  A chain
P = (k = x_0, x_1, ..., x_t), t >= 1, follows the official rule of k4/sdc.md §29 (k4/sdc/oc1_mc2_rand.Inst.moves):
x_i (i >= 1) takes {y_{x_{i-1}}} + H_i with H_i junk and v_{x_i} rising; k takes H0 from the unused junk and y_{x_t},
v_k(H0) > p_k.  Here k is dangerous, and the end x_t is unfrozen at Y or gives its pick to k (y_{x_t} in H0).
B' is the state after P, J' its junk.

For an owner o in {k, x_t} the exchange value is
  d_o(P, H0) = min over kept-out sets H, subsets of J', of |H| - nu(Gamma(H))
subject to
  (1') X = B'_o + (J' - H) threatens no frozen agent of Y off P at its pick value, and no chain agent other than o
       at its value in B';
  (G1') no multi-good bundle of B' other than o's threatens anybody at B' values;
  (2) every holder of Y off P threatened by X at its pick value (exposed) is matched in Gamma(H) to a good that
      makes it safe;
where Gamma(H) is Lemma 2*'s slot graph of Y: H against the holders of Y off P (exposure at pick values).  The
chain also supplies s_o free slots: the agents other than o that are x_t or frozen at Y, and are unfrozen single-good
holders at B'.
For o = k and a chain without junk for x_1..x_t this is Lemma 2*'s deficiency of Y for the owner set W_{x_t} = J +
{y_{x_t}} with k's demand deleted (the chain is an exchange in the slot graph: ownership moves from the end to k, k's
demand disappears, s_k slots appear).
Lemma EX (k4/matching.md §3, written proof): d_o(P, H0) <= s_o implies an S* completion of B' owned by o.
This script checks EX on every such (P, H0, o) at every hard start (the proof's allocation is built and checked
against raw EFX0, and compared with the raw completion test) and counts the hard starts satisfying Conjecture CM:
some (P, H0, o) with d_o <= s_o.

    python3 k4/matching/exchange.py FILE.jsonl [FILE.jsonl ...]      (rows of hard_starts.py)"""
import sys, os, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, INF, subsets, bip_match


def canonical_chains(I, base):
    """Chains from a dangerous agent along wants (x_i wants y_{x_{i-1}}), ending at an agent unfrozen at Y."""
    Y = [b[0] if b else None for b in base]; fz = set(I.frozen(base)); out = []

    def ext(path):
        x = path[-1]
        for w in range(I.n):
            if w in path or Y[w] is None or not I.wants(w, Y[x], base): continue
            p2 = path + [w]
            if w not in fz: out.append(p2)
            else: ext(p2)
    for k in I.dangerous(base): ext([k])
    return out


def general_chains(I, base):
    """Official chains from a dangerous agent to an end with a nonempty base; yields (P, Hs) with Hs[i] = H_i."""
    J = I.junk(base); out = []

    def ext(path, used, Hs):
        x = path[-1]
        if not base[x]: return
        for w in range(I.n):
            if w in path: continue
            for H in subsets([g for g in J if g not in used and g in I.R[w]]):
                if I.V(w, base[x] + list(H)) > I.V(w, base[w]):
                    Hs2 = dict(Hs); Hs2[len(path)] = list(H); p2 = path + [w]
                    if base[w]: out.append((p2, Hs2))
                    if len(p2) < I.n: ext(p2, used | set(H), Hs2)
    for k in I.dangerous(base): ext([k], frozenset(), {})
    return out


def apply_chain(I, base, P, H0, Hs=None):
    Hs = Hs or {}; nb = [list(b) for b in base]; nb[P[0]] = list(H0)
    for i in range(1, len(P)): nb[P[i]] = list(base[P[i - 1]]) + list(Hs.get(i, ()))
    return nb


def ex_value(I, base, P, Bp, o, build=False):
    """(d_o, s_o, why, witness) for the chain P (state Bp after it) and any owner o (on P or off it)."""
    Jp = I.junk(Bp); bv = [I.V(i, base[i]) for i in range(I.n)]
    fz = set(I.frozen(base)); fzB = set(I.frozen(Bp)); bvB = [I.V(i, Bp[i]) for i in range(I.n)]
    extra = [j for j in range(I.n) if j != o and (j == P[-1] or j in fz) and j not in fzB and len(Bp[j]) == 1]
    s = len(extra)
    for j in range(I.n):
        if j != o and len(Bp[j]) >= 2 and any(i != j and I.threat(i, Bp[j], bvB[i]) for i in range(I.n)):
            return INF, s, 'G1', None
    N1 = [u for u in I.holders(base) if u not in P and u != o]
    off_frozen = [q for q in fz if q not in P and q != o]; chain_others = [x for x in P if x != o]
    best, wit, why = INF, None, 'no H'
    for H in subsets(Jp):
        X = list(Bp[o]) + [g for g in Jp if g not in H]
        if any(I.threat(q, X, bv[q]) for q in off_frozen): continue
        if any(I.threat(x, X, bvB[x]) for x in chain_others):
            why = 'chain agent threatened'; continue
        E = [u for u in N1 if I.threat(u, X, bv[u])]
        adj = {h: [u for u in N1 if u not in E or
                   (I.v[u].get(h, 0) > 0 and not I.threat(u, X, bv[u] + I.v[u][h]))] for h in H}
        radj = {u: [h for h in H if u in adj[h]] for u in E}
        if len(bip_match(E, radj)) < len(E): continue
        df = len(H) - len(bip_match(H, adj))
        if df < best:
            best = df
            wit = md_witness(I, Bp, o, X, H, N1, E, adj, extra) if build and df <= s else None
    return best, s, ('ok' if best < INF else why), wit


def md_witness(I, Bp, o, X, H, N1, E, adj, extra):
    """The allocation of Lemma EX's proof: X to o; H placed into N1 (covering every exposed holder, each with an
    admissible good) and the extra slots (any good).  Mendelsohn-Dulmage guarantees one; found here by search."""
    slots = list(N1) + list(extra); H = list(H)

    def dfs(i, used, asg):
        if i == len(H):
            return None if any(u not in used for u in E) else dict(asg)
        h = H[i]
        for u in slots:
            if u in used or (u in N1 and u not in adj[h]): continue
            used.add(u); asg[h] = u
            r = dfs(i + 1, used, asg)
            used.discard(u); del asg[h]
            if r is not None: return r
        return None
    asg = dfs(0, set(), {})
    if asg is None: return None
    Xall = [list(b) for b in Bp]; Xall[o] = list(X)
    for h, u in asg.items(): Xall[u].append(h)
    return Xall


def job(row):
    I = M(row['sets'], row['vals'], row['m'], row['name']); Y = row['picks']
    base = [[g] if g is not None else [] for g in Y]; J = I.junk(base); fz = set(I.frozen(base))
    C = collections.Counter(); info = []
    best = {'canonical, owner k': False, 'any chain, owner k': False, 'any chain, owner k or end': False,
            'any chain, any owner': False}
    canon = set(tuple(P) for P in canonical_chains(I, base))
    for P, Hs in general_chains(I, base):
        k, xt = P[0], P[-1]; used = set(g for h in Hs.values() for g in h)
        Pi = [g for g in J if g not in used] + [Y[xt]]
        kind = 'canonical' if tuple(P) in canon and not any(Hs.values()) else 'general'
        for H0 in subsets([g for g in Pi if g in I.R[k]], 1):
            if I.V(k, H0) <= I.V(k, base[k]): continue
            if xt in fz and Y[xt] not in H0: continue
            Bp = apply_chain(I, base, P, list(H0), Hs)
            for o in range(I.n):
                oname = 'k' if o == k else 'end' if o == xt else 'off-chain'
                d, s, why, wit = ex_value(I, base, P, Bp, o, build=True)
                ok = d <= s
                rep = I.complete(Bp, 0, 'ss', [o]) is not None
                C['%s chains, owner %s: EX hypothesis %s, S* completion owned by o %s' % (kind, oname, ok, rep)] += 1
                if not ok and d >= INF: C['%s chains, owner %s: d = INF (%s)' % (kind, oname, why)] += 1
                if ok:
                    shape_ok = wit is not None and I.efx0(wit)
                    if not shape_ok:
                        C['EX WITNESS FAILS'] += 1; info.append(('EX WITNESS FAILS', P, H0, Hs, o))
                    if not rep:
                        C['EX VIOLATION'] += 1; info.append(('EX VIOLATION', P, H0, Hs, o))
                    if oname == 'k':
                        best['any chain, owner k'] = True
                        if kind == 'canonical': best['canonical, owner k'] = True
                    if oname != 'off-chain': best['any chain, owner k or end'] = True
                    best['any chain, any owner'] = True
    return row, C, best, info


if __name__ == '__main__':
    print('$ python3 k4/matching/exchange.py', *[os.path.relpath(f, _mpaths.ROOT) for f in sys.argv[1:]], flush=True)
    rows = [json.loads(l) for f in sys.argv[1:] for l in open(f)]
    T = collections.Counter(); t0 = time.time(); fails = collections.defaultdict(list)
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for row, C, best, info in pool.imap_unordered(job, rows, chunksize=4):
            T.update(C); T['hard starts'] += 1
            for form, ok in best.items():
                T['hard starts, delta_oa = %d: CM (%s) %s' % (row['d_oa'], form, 'holds' if ok else 'FAILS')] += 1
                if not ok: fails[form].append(row)
            for x in info:
                print(x[0], row['name'], json.dumps([row['sets'], row['vals']]), 'picks', row['picks'], 'P', x[1],
                      'H0', x[2], 'Hs', x[3], 'owner', x[4], flush=True)
    for k in sorted(T): print(k, T[k])
    for form in sorted(fails):
        L = sorted(fails[form], key=lambda r: (len(r['sets']), r['m']))
        print('CM (%s) fails on %d hard starts; smallest:' % (form, len(L)))
        for r in L[:5]:
            print('   ', r['name'], 'n', len(r['sets']), 'm', r['m'], 'd_oa', r['d_oa'],
                  json.dumps([r['sets'], r['vals']]), 'picks', r['picks'])
    print('time %.0f s' % (time.time() - t0))


# ---- Lemma EX* (k4/matching.md §5): the exchange at any state with unwanted junk ------------------------------------
def all_chains(I, base, starts=None):
    """Official chains (x_i takes B_{x_{i-1}} + H_i, improving; never handing on an empty base) from the given start
    agents (default: everybody) to any end; yields (P, Hs)."""
    J = I.junk(base); out = []

    def ext(path, used, Hs):
        x = path[-1]
        if not base[x]: return
        for w in range(I.n):
            if w in path: continue
            for H in subsets([g for g in J if g not in used and g in I.R[w]]):
                if I.V(w, list(base[x]) + list(H)) > I.V(w, base[w]):
                    Hs2 = dict(Hs); Hs2[len(path)] = list(H); p2 = path + [w]
                    out.append((p2, Hs2))
                    if len(p2) < I.n: ext(p2, used | set(H), Hs2)
    for k in (range(I.n) if starts is None else starts): ext([k], frozenset(), {})
    return out


def ex_value_general(I, base, P, Bp, o):
    """Lemma EX* at an arbitrary state `base` with the chain P (state Bp after it) and owner o.  Returns (d, s, why):
    d = min over H (subset of J') of |H| - nu(Gamma_B(H)) subject to
      (W')  every good of J' is unwanted at Bp;
      (G1') no multi-good bundle of Bp other than o's threatens anybody at Bp values;
      (1')  X = Bp_o + (J' - H) threatens no non-holder of `base` off P (other than o) at its value in `base`, and no
            chain agent other than o at its value in Bp;
      (2)   the exposed holders of `base` off P (other than o) are coverable by compensating goods;
    s = number of holders of Bp other than o that are not holders of `base` off P (the slots the chain creates).
    EX*: d <= s implies an S* completion of Bp owned by o."""
    Jp = I.junk(Bp); bv = [I.V(i, base[i]) for i in range(I.n)]; bvB = [I.V(i, Bp[i]) for i in range(I.n)]
    hold = set(I.holders(base)); holdB = set(I.holders(Bp))
    N1 = [u for u in sorted(hold) if u not in P and u != o]
    extra = [j for j in sorted(holdB) if j != o and j not in N1]; s = len(extra)
    if any(I.v[i].get(g, 0) > bvB[i] for g in Jp for i in range(I.n)): return INF, s, 'W'
    for j in range(I.n):
        if j != o and len(Bp[j]) >= 2 and any(i != j and I.threat(i, Bp[j], bvB[i]) for i in range(I.n)):
            return INF, s, 'G1'
    Qoff = [q for q in range(I.n) if q not in P and q != o and q not in hold]
    chain_others = [x for x in P if x != o]; best = INF; why = 'no H'
    for H in subsets(Jp):
        X = list(Bp[o]) + [g for g in Jp if g not in H]
        if any(I.threat(q, X, bv[q]) for q in Qoff): continue
        if any(I.threat(x, X, bvB[x]) for x in chain_others): why = 'chain agent threatened'; continue
        E = [u for u in N1 if I.threat(u, X, bv[u])]
        adj = {h: [u for u in N1 if u not in E or
                   (I.v[u].get(h, 0) > 0 and not I.threat(u, X, bv[u] + I.v[u][h]))] for h in H}
        radj = {u: [h for h in H if u in adj[h]] for u in E}
        if len(bip_match(E, radj)) < len(E): continue
        df = len(H) - len(bip_match(H, adj))
        if df < best: best = df
    return best, s, ('ok' if best < INF else why)


def ex_star_witness(I, base, starts=None):
    """Some (P, H0, Hs, owner) at `base` satisfying EX*'s hypothesis, or None."""
    J = I.junk(base)
    for P, Hs in all_chains(I, base, starts):
        k, xt = P[0], P[-1]; used = set(g for h in Hs.values() for g in h)
        pool = [g for g in J if g not in used] + list(base[xt])
        for H0 in subsets([g for g in pool if g in I.R[k]], 1):
            if I.V(k, H0) <= I.V(k, base[k]): continue
            Bp = apply_chain(I, base, P, list(H0), Hs)
            for o in range(I.n):
                d, s, _ = ex_value_general(I, base, P, Bp, o)
                if d <= s: return P, list(H0), Hs, o, Bp
    return None
