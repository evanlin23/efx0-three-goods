"""Candidate goods-first / envy-graph algorithms for EFX0 with at most three relevant goods per agent. Evidence only.

Families (each returns X[g] = agent):
  ece(order, pick, safe)       Lipton envy-cycle elimination: goods one at a time in `order`; rotate envy cycles
                               (F2); give the good to a source of the envy graph chosen by `pick`. With safe=True,
                               prefer a source (then any agent) to which adding the good keeps EFX0.
  srcpick(rule, safe)          dynamic picking sequence: rotate cycles; a source that still values a pool good picks
                               its favourite pool good; goods nobody left can pick go by ece's safe rule.
  draft_env(draft, lo, order)  one good each (K3S's draft: peelable agents first, else a leader by index; or plain
                               serial dictatorship), then each leftover good goes, after cycle rotation, to an
                               agent for which EFX0 is kept, by rule `lo`.
  topval(tie, rest)            each good to a valuer ranking it highest (tie rule), worthless goods to a source.
"""
from common import ranking, bval, threat, eliminate_cycles, sources, to_X, envy, all_safe

# ------------------------------------------------------------------------------------------- good orders
def goods_order(order, n, m, v, rk):
    deg = [0] * m; cnt = [[0, 0, 0] for _ in range(m)]; best = [3] * m
    for i in range(n):
        for t, g in enumerate(rk[i]):
            deg[g] += 1
            if t < 3: cnt[g][t] += 1
            best[g] = min(best[g], t)
    key = {
        'idx': lambda g: g,
        'deg_desc': lambda g: (-deg[g], g),
        'deg_asc': lambda g: (deg[g] == 0, deg[g], g),
        'top': lambda g: (-cnt[g][0], -cnt[g][1], -cnt[g][2], g),
        'bestpos': lambda g: (best[g], -deg[g], g),
        'bestpos_asc': lambda g: (best[g], deg[g], g),
        'worstfirst': lambda g: (deg[g] == 0, -best[g], g),
        'valsum': lambda g: (-sum(v[i].get(g, 0) for i in range(n)), g),
    }[order]
    return sorted(range(m), key=key)

def keeps(n, v, B, s, g):
    """adding g to B[s] keeps every other agent safe toward s's bundle"""
    nb = B[s] + [g]
    return all(bval(v[i], B[i]) >= threat(v[i], nb) for i in range(n) if i != s)

def choose(cands, pick, v, B, g):
    if pick == 'idx': return min(cands)
    if pick == 'bestval': return min(cands, key=lambda s: (-v[s].get(g, 0), s))
    if pick == 'leastval': return min(cands, key=lambda s: (v[s].get(g, 0), s))
    if pick == 'poorest': return min(cands, key=lambda s: (bval(v[s], B[s]), s))
    if pick == 'fewest': return min(cands, key=lambda s: (len(B[s]), -v[s].get(g, 0), s))
    raise ValueError(pick)

# ------------------------------------------------------------------------------------------- ECE
def ece(order='idx', pick='bestval', safe=False, anyagent=True):
    def alg(n, m, v):
        rk = ranking(v); B = [[] for _ in range(n)]
        for g in goods_order(order, n, m, v, rk):
            E = eliminate_cycles(n, v, B); S = sources(n, E); cand = S
            if safe:
                ok = [s for s in S if keeps(n, v, B, s, g)]
                if not ok and anyagent: ok = [s for s in range(n) if keeps(n, v, B, s, g)]
                if ok: cand = ok
            B[choose(cand, pick, v, B, g)].append(g)
        eliminate_cycles(n, v, B)
        return to_X(m, B)
    alg.__name__ = f"ece[{order},{pick},{'safe' if safe else 'plain'}]"
    return alg

# ------------------------------------------------------------------------------------------- source picks
def srcpick(rule='idx', safe=True):
    """a source of the envy graph that values some pool good picks its favourite one (if safe=True: only picks that
    keep EFX0; an agent may pick a lower good of its own if its favourite is unsafe? no: favourite only)"""
    def alg(n, m, v):
        rk = ranking(v); B = [[] for _ in range(n)]; pool = set(range(m))
        while True:
            E = eliminate_cycles(n, v, B); S = sources(n, E)
            opts = []
            for s in S:
                fav = next((g for g in rk[s] if g in pool), None)
                if fav is None: continue
                if safe and not keeps(n, v, B, s, fav): continue
                opts.append((s, fav))
            if not opts: break
            if rule == 'idx': s, g = opts[0]
            elif rule == 'poorest': s, g = min(opts, key=lambda o: (bval(v[o[0]], B[o[0]]), o[0]))
            elif rule == 'fewest': s, g = min(opts, key=lambda o: (len(B[o[0]]), o[0]))
            elif rule == 'favval': s, g = min(opts, key=lambda o: (-v[o[0]][o[1]], o[0]))
            B[s].append(g); pool.discard(g)
        for g in sorted(pool):
            E = eliminate_cycles(n, v, B); S = sources(n, E)
            ok = [s for s in S if keeps(n, v, B, s, g)] or [s for s in range(n) if keeps(n, v, B, s, g)] or S
            B[choose(ok, 'bestval', v, B, g)].append(g)
        return to_X(m, B)
    alg.__name__ = f"srcpick[{rule},{'safe' if safe else 'plain'}]"
    return alg

# ------------------------------------------------------------------------------------------- draft + envy leftovers
def k3s_draft(n, m, v, rk):
    free = set(range(m)); unproc = list(range(n)); Y = [None] * n; order = []
    def peel(i):
        fr = [g for g in rk[i] if g in free]
        return not fr or v[i][fr[0]] >= sum(v[i][g] for g in fr[1:])
    while unproc:
        i = next((j for j in unproc if peel(j)), unproc[0])
        Y[i] = next((g for g in rk[i] if g in free), None); free.discard(Y[i]); order.append(i); unproc.remove(i)
    return Y, order, free

def sd_draft(n, m, v, rk):
    free = set(range(m)); Y = [None] * n
    for i in range(n):
        Y[i] = next((g for g in rk[i] if g in free), None); free.discard(Y[i])
    return Y, list(range(n)), free

def draft_env(draft='k3s', lo='valuer', order='idx', rotate=True):
    """lo rules for a leftover g (only agents to which adding g keeps EFX0 are candidates):
       'valuer'   : a valuer of g (highest-ranked position, then index), else a source, else anyone
       'source'   : a source (valuer first), else anyone
       'lastsrc'  : a source latest in the draft order, else anyone
       'nonvaluer': a source that does not value g, else a source, else anyone"""
    def alg(n, m, v):
        rk = ranking(v)
        Y, dorder, free = (k3s_draft if draft == 'k3s' else sd_draft)(n, m, v, rk)
        B = [[] if Y[i] is None else [Y[i]] for i in range(n)]
        if lo.startswith('greedy'):
            place_pool(n, m, v, B, free, lo, rotate, rk)
            return to_X(m, B)
        pos = [{g: t for t, g in enumerate(rk[i])} for i in range(n)]
        left = goods_order(order, n, m, v, rk); left = [g for g in left if g in free]
        for g in left:
            E = eliminate_cycles(n, v, B) if rotate else envy(n, v, B); S = sources(n, E)
            ok = [s for s in range(n) if keeps(n, v, B, s, g)]
            okS = [s for s in S if s in ok]
            if lo == 'valuer':
                val = [s for s in ok if g in v[s]]
                cand = sorted(val, key=lambda s: (pos[s][g], s)) or okS or ok or S
                s = cand[0]
            elif lo == 'source':
                cand = okS or ok or S; s = choose(cand, 'bestval', v, B, g)
            elif lo == 'lastsrc':
                cand = okS or ok or S; s = max(cand, key=dorder.index)
            elif lo == 'nonvaluer':
                cand = [s for s in okS if g not in v[s]] or okS or ok or S; s = max(cand, key=dorder.index)
            B[s].append(g)
        return to_X(m, B)
    alg.__name__ = f"draft_env[{draft},{lo},{order}{'' if rotate else ',norot'}]"
    return alg

# ------------------------------------------------------------------------------------------- top valuer
def topval(tie='idx', order='bestpos'):
    """each valued good to a valuer ranking it highest (ties: lowest index, or fewest goods so far); worthless goods to
    a source (L3) after rotating cycles"""
    def alg(n, m, v):
        rk = ranking(v); pos = [{g: t for t, g in enumerate(rk[i])} for i in range(n)]
        B = [[] for _ in range(n)]; junk = []
        for g in goods_order(order, n, m, v, rk):
            val = [i for i in range(n) if g in v[i]]
            if not val: junk.append(g); continue
            bp = min(pos[i][g] for i in val); cand = [i for i in val if pos[i][g] == bp]
            if tie == 'idx': s = min(cand)
            elif tie == 'fewest': s = min(cand, key=lambda i: (len(B[i]), i))
            elif tie == 'poorest': s = min(cand, key=lambda i: (bval(v[i], B[i]), i))
            B[s].append(g)
        for g in junk:
            E = eliminate_cycles(n, v, B); S = sources(n, E); B[S[0]].append(g)
        eliminate_cycles(n, v, B)
        return to_X(m, B)
    alg.__name__ = f"topval[{tie},{order}]"
    return alg

# ------------------------------------------------------------------------------------------- EP (ep.py), by name
def epv(place='greedy', **kw):
    from ep import ep
    def alg(n, m, v): return ep(n, m, v, place=place, **kw)
    alg.__name__ = f"ep[{place}{''.join(f',{k}={x}' for k, x in kw.items())}]"
    return alg

# ------------------------------------------------------------------------------------------- envy the pool (charity)
def minimal_envied(n, v, B, i, Z):
    """shrink Z (envied by i) to a minimal envied set: drop a good while some agent still envies the rest; returns
    (agent, Z) with Z envied by agent and no agent envying Z minus any one good"""
    Z = list(Z)
    changed = True
    while changed:
        changed = False
        for g in sorted(Z, key=lambda g: (v[i].get(g, 0), g)):
            Zg = [h for h in Z if h != g]
            if not Zg: continue
            j = next((j for j in range(n) if bval(v[j], Zg) > bval(v[j], B[j])), None)
            if j is not None:
                Z, i, changed = Zg, j, True
                break
    return i, Z

def place_pool(n, m, v, B, P, place, rot=True, rk=None):
    """each pool good, after rotating cycles, to an agent for which EFX0 is kept (rule `place`)"""
    rk = rk or ranking(v); pos = [{g: t for t, g in enumerate(rk[i])} for i in range(n)]
    if place.startswith('greedy'):
        # 'greedy': while some agent values a pool good and can take it keeping EFX0, it does (best-ranked first);
        # otherwise one pool good goes to a source for which EFX0 is kept ('greedy': lowest good index first,
        # source by index; 'greedy_nv': prefer a source that does not value it; 'greedy_last': the last source)
        P = set(P)
        while P:
            E = eliminate_cycles(n, v, B) if rot else envy(n, v, B); S = sources(n, E)
            up = [(pos[s][g], s, g) for g in P for s in range(n) if g in v[s] and keeps(n, v, B, s, g)]
            if up:
                _, s, g = min(up); B[s].append(g); P.discard(g); continue
            opts = [(g, s) for g in sorted(P) for s in S if keeps(n, v, B, s, g)]
            if place == 'greedy_nv':
                opts.sort(key=lambda o: (o[0] in v[o[1]], o[0], o[1]))
            elif place == 'greedy_last':
                opts.sort(key=lambda o: (o[0], -o[1]))
            if not opts:
                opts = [(g, s) for g in sorted(P) for s in range(n) if keeps(n, v, B, s, g)] or [(min(P), S[0])]
            g, s = opts[0]; B[s].append(g); P.discard(g)
        return
    for g in sorted(P):
        E = eliminate_cycles(n, v, B) if rot else envy(n, v, B); S = sources(n, E)
        ok = [s for s in range(n) if keeps(n, v, B, s, g)]
        okS = [s for s in S if s in ok]
        if place == 'valuer':
            val = [s for s in ok if g in v[s]]
            cand = sorted(val, key=lambda s: (pos[s][g], s)) or okS or ok or S
        elif place == 'source':
            cand = sorted(okS, key=lambda s: (-v[s].get(g, 0), s)) or ok or S
        elif place == 'nonvaluer':
            cand = [s for s in okS if g not in v[s]] or okS or ok or S
        B[cand[0]].append(g)

def envypool(pick='idx', place='valuer', rot=True):
    """maintain an EFX0 partial allocation; while some agent envies the pool, give a minimal envied subset Z of the
    pool to an agent envying it (that keeps EFX0: nobody envies Z minus a good) and return its old bundle to the
    pool; rotate envy cycles. When nobody envies the pool, place each pool good with an agent for which EFX0 is
    kept (rule `place`).
    pick: 'idx' (smallest index that envies the pool), 'poorest' (smallest own value), 'last' (largest index),
          'single' (prefer an agent envying a single good; else idx)."""
    def alg(n, m, v):
        rk = ranking(v)
        B = [[] for _ in range(n)]; P = set(range(m)); steps = 0
        while True:
            if rot: eliminate_cycles(n, v, B)
            env = [i for i in range(n) if bval(v[i], P) > bval(v[i], B[i])]
            if not env: break
            steps += 1
            if steps > 10000: return None
            if pick == 'idx': i = env[0]
            elif pick == 'last': i = env[-1]
            elif pick == 'poorest': i = min(env, key=lambda i: (bval(v[i], B[i]), i))
            elif pick == 'single':
                one = [i for i in env if any(v[i].get(g, 0) > bval(v[i], B[i]) for g in P)]
                i = (one or env)[0]
            elif pick in ('peel', 'peel_last', 'peel_poor'):
                # R1 priority: an envier whose favourite pool good is worth at least its other pool goods together
                def pl(i):
                    fr = [v[i][g] for g in rk[i] if g in P]
                    return not fr or fr[0] >= sum(fr[1:])
                pe = [i for i in env if pl(i)]
                if pick == 'peel': i = (pe or env)[0]
                elif pick == 'peel_last': i = pe[0] if pe else env[-1]
                else: i = min(pe or env, key=lambda i: (bval(v[i], B[i]), i))
            elif pick.startswith('draft'):
                # finish the one-good draft first (empty-handed peelable agents, then an empty-handed leader by
                # index), then swaps with the pool: 'draft' by index, 'draft_poor' poorest first, 'draft_last' last
                def pl(i):
                    fr = [v[i][g] for g in rk[i] if g in P]
                    return not fr or fr[0] >= sum(fr[1:])
                emp = [i for i in env if not B[i]]
                pe = [i for i in emp if pl(i)]
                if pe: i = pe[0]
                elif emp: i = emp[0]
                elif pick == 'draft': i = env[0]
                elif pick == 'draft_last': i = env[-1]
                else: i = min(env, key=lambda i: (bval(v[i], B[i]), i))
            Z = [g for g in rk[i] if g in P]
            for t in range(1, len(Z) + 1):          # the shortest envied prefix of i's ranking within the pool
                if bval(v[i], Z[:t]) > bval(v[i], B[i]): Z = Z[:t]; break
            j, Z = minimal_envied(n, v, B, i, Z)
            P |= set(B[j]); B[j] = list(Z); P -= set(Z)
        place_pool(n, m, v, B, P, place, rot, rk)
        return to_X(m, B)
    alg.__name__ = f"envypool[{pick},{place}{'' if rot else ',norot'}]"
    return alg
