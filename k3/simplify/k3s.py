"""K3S: a simplified K3ALG (branch proof/k3-simplify). Candidate; correctness here is EVIDENCE only.

Input: n agents, m goods, v[i] = {good: positive value}, at most three goods per agent (others worth 0).

  1. Draft. Agents take turns; each takes its favourite remaining good (or nothing). Next is an agent that
     "can be peeled": its favourite remaining good is worth at least all its other remaining goods together (true
     for anyone who lost a good, values at most two goods, or is top-heavy). If there is none, any agent goes
     (a "leader"; it takes its top).
  2. Upgrades. While some agent holds its second good b, its third good c is left over, and nobody needs b alone,
     it also takes c. (Only for agents with three goods and a <= b + c.)
  3. Absorber. r = the last agent of the draft that was not upgraded. An agent x != r is "exposed" if it is strictly
     balanced (a < b + c), not upgraded, holds its top, and its other two goods are each left over or r's. Put one of those goods per exposed agent (HitSet) into the
     bundles of "free" agents other than r, one good each (free: not upgraded, and nobody needs its good alone);
     r takes every other leftover.
  4. Rotation, if the slots are too few: k = the last exposed agent gives its top to an agent that needs it, whose
     old good goes to an agent that needs that, ... (a need chain); k takes its b and c and becomes the absorber.

On instances where every agent values at most two goods, nobody is ever a leader, upgraded or exposed, so K3S is
exactly serial dictatorship with the last agent taking all leftovers (Corollary L2c).

Differences from K3ALG: no separate peeling stage (step 1 does it); the absorber always takes all leftovers but
HitSet (K3ALG fills every free slot first and uses no absorber when everything fits); one slot per free agent (K3ALG:
two for an agent without a good); k* is "the last exposed agent" (no blocks). cap1=False restores K3ALG's slots;
single_pass=True replaces the upgrade loop by one pass in draft order (a WRONG variant, attempts/k3s-single-pass-upgrades.md).
"""
import sys

def k3s(n, m, v, info=None, cap1=True, single_pass=False, strict_absorb=True, leader='index', rotate=True):
    # rankings: relevant goods by value, largest first, ties by index
    rk = [sorted(v[i], key=lambda g: (-v[i][g], g)) for i in range(n)]
    pos = [{g: t for t, g in enumerate(rk[i])} for i in range(n)]
    def top_heavy(i): return len(rk[i]) < 3 or v[i][rk[i][0]] >= v[i][rk[i][1]] + v[i][rk[i][2]]
    def balanced3(i): return len(rk[i]) == 3 and v[i][rk[i][0]] <= v[i][rk[i][1]] + v[i][rk[i][2]]
    def strict3(i): return len(rk[i]) == 3 and v[i][rk[i][0]] < v[i][rk[i][1]] + v[i][rk[i][2]]

    # 1. draft
    free = set(range(m)); unproc = list(range(n)); order = []; Y = [None] * n
    def peelable(i, free=free):
        fr = [g for g in rk[i] if g in free]
        return not fr or v[i][fr[0]] >= sum(v[i][g] for g in fr[1:])
    lead = LEADERS[leader] if isinstance(leader, str) else leader
    ctx = dict(rk=rk, pos=pos, v=v, n=n, peelable=peelable, strict3=strict3, balanced3=balanced3)
    while unproc:
        i = next((j for j in unproc if peelable(j)), None)
        if i is None:
            i = lead(ctx, unproc, free, Y)
            if info is not None: info.setdefault('leaders', []).append(i)
        Y[i] = next((g for g in rk[i] if g in free), None)
        free.discard(Y[i]); order.append(i); unproc.remove(i)

    def needs(i, Y, U):
        if i in U: return ()
        if Y[i] is None: return rk[i]
        return rk[i][:pos[i][Y[i]]]
    def NA(Y, U): return {g for i in range(n) for g in needs(i, Y, U)}
    def junk(Y, U):
        used = {g for g in Y if g is not None} | {rk[u][2] for u in U}
        return [g for g in range(m) if g not in used]
    def caps(Y, U):
        na = NA(Y, U)
        return [0 if (i in U or (Y[i] is not None and Y[i] in na)) else (2 if Y[i] is None and not cap1 else 1) for i in range(n)]

    # 2. upgrades
    U = []
    if single_pass:
        for k in order:
            if balanced3(k) and Y[k] == rk[k][1] and rk[k][2] in set(junk(Y, U)) and rk[k][1] not in NA(Y, U):
                U.append(k)
    while not single_pass:
        J = set(junk(Y, U)); na = NA(Y, U)
        k = next((k for k in range(n) if k not in U and balanced3(k) and Y[k] == rk[k][1]
                  and rk[k][2] in J and rk[k][1] not in na), None)
        if k is None: break
        U.append(k)

    def exposed(o, Y, U):
        W = set(junk(Y, U)) | ({rk[o][1], rk[o][2]} if o in U else ({Y[o]} if Y[o] is not None else set()))
        return [x for x in range(n) if x != o and x not in U and strict3(x) and Y[x] == rk[x][0]
                and rk[x][1] in W and rk[x][2] in W]
    def hitset(E, Y, U):
        J = set(junk(Y, U))
        one = lambda z: rk[z][1] if rk[z][1] in J else rk[z][2]
        for x in E:
            for y in E:
                if x != y:
                    for g in (rk[x][1], rk[x][2]):
                        if g in J and g in (rk[y][1], rk[y][2]):
                            return [g] + [one(z) for z in E if z not in (x, y)]
        return [one(z) for z in E]
    def absorb(o, Y, U):
        """None if o cannot absorb (HitSet does not fit the other agents' slots); else the allocation."""
        E = exposed(o, Y, U); J = junk(Y, U); cap = caps(Y, U)
        if any(rk[z][1] not in J and rk[z][2] not in J for z in E):
            if strict_absorb: return None          # never happens for K3S (Lemma lead, Theorem B (f))
            E = [z for z in E if rk[z][1] in J or rk[z][2] in J]   # variants: build the allocation anyway
        H = list(dict.fromkeys(hitset(E, Y, U)))
        if len(H) > sum(cap) - cap[o]: return None
        X = [None] * m
        for i in range(n):
            if Y[i] is not None: X[Y[i]] = i
        for u in U: X[rk[u][2]] = u
        for i in range(n):
            if i == o: continue
            for g in H[:cap[i]]: X[g] = i
            H = H[cap[i]:]
        for g in J:
            if X[g] is None: X[g] = o
        return X

    # 3. absorber r
    r = [i for i in order if i not in U][-1]
    X = absorb(r, Y, U)
    if X is not None:
        if info is not None: info['branch'] = 'r'
        return X
    # 4. rotation
    if not rotate:
        if info is not None: info['branch'] = 'needs_rotation'
        return None
    E = exposed(r, Y, U); k = max(E, key=order.index)
    na = NA(Y, U); chain = [k]
    for j in order[order.index(k) + 1:]:
        cur = chain[-1]
        if (Y[cur] is not None and Y[cur] in na and j not in U
                and pos[j].get(Y[cur], 9) < (9 if Y[j] is None else pos[j][Y[j]])):
            chain.append(j)
    Y2 = list(Y)
    for s in range(1, len(chain)): Y2[chain[s]] = Y[chain[s - 1]]
    Y2[k] = rk[k][1]; U2 = U + [k]
    X = absorb(k, Y2, U2)
    if info is not None: info['branch'] = 'rot'; info['chain_ends_at_r'] = chain[-1] == r; info['chain'] = chain; info['r'] = r
    return X

# ------------------------------------------------------------------------------------------- leader rules (step 1)
def sim_block(ctx, x, unproc, free, Y):
    """x leads: takes its top; then agents that can be peeled go, until none can. Returns the state and the block."""
    rk, peel = ctx['rk'], ctx['peelable']
    unproc, free, Y = list(unproc), set(free), list(Y); blk = []
    c = x
    while c is not None:
        Y[c] = next((g for g in rk[c] if g in free), None); free.discard(Y[c]); unproc.remove(c); blk.append(c)
        c = next((j for j in unproc if peel(j, free)), None)
    return unproc, free, Y, blk

def block_needs(ctx, blk, Y):
    """goods needed by the agents of a block (by (B1) no later agent values a good picked in it)"""
    rk, pos = ctx['rk'], ctx['pos']
    return {g for i in blk for g in (rk[i] if Y[i] is None else rk[i][:pos[i][Y[i]]])}

def safe_free(ctx, blk, Y):
    """agents of the block that are free at its end and can never be upgraded (hold their top, their c, or
    nothing); needs only shrink later, so they stay free"""
    rk = ctx['rk']; na = block_needs(ctx, blk, Y)
    return [i for i in blk if (Y[i] is None or Y[i] not in na) and (Y[i] is None or len(rk[i]) < 2 or Y[i] != rk[i][1])]

def provable(ctx, x, unproc, free, Y):
    """Lemma T: if x's block ends with two free agents that stay free, or x can never be exposed (its b and c are
    tops of two other unprocessed agents), then r is a valid absorber at the end, whatever happens later."""
    rk = ctx['rk']
    tops = {rk[y][0] for y in unproc if y != x}
    if rk[x][1] in tops and rk[x][2] in tops: return True
    _, _, Y2, blk = sim_block(ctx, x, unproc, free, Y)
    return len(safe_free(ctx, blk, Y2)) >= 2

def lead_index(ctx, unproc, free, Y): return unproc[0]

def na_after(ctx, x, unproc, free, Y):
    """construction LB's lookahead count: |NA| over processed agents after x's block, minus certain upgrades"""
    rk, pos, n = ctx['rk'], ctx['pos'], ctx['n']
    un2, fr2, Y2, _ = sim_block(ctx, x, unproc, free, Y)
    done = [k for k in range(n) if k not in un2]
    junk = {g for g in fr2 if not any(g in rk[k] for k in un2)}
    up = set()
    while True:
        NA = {g for k in done if k not in up for g in (rk[k] if Y2[k] is None else rk[k][:pos[k][Y2[k]]])}
        k = next((k for k in done if k not in up and ctx['balanced3'](k) and Y2[k] == rk[k][1] and rk[k][2] in junk
                  and rk[k][1] not in NA), None)
        if k is None: return len(NA)
        up.add(k); junk.discard(rk[k][2])

def lead_lb(ctx, unproc, free, Y): return min(unproc, key=lambda x: (na_after(ctx, x, unproc, free, Y), x))

def lead_P(ctx, unproc, free, Y):
    return next((x for x in unproc if provable(ctx, x, unproc, free, Y)), unproc[0])

def lead_P_lb(ctx, unproc, free, Y):
    return next((x for x in unproc if provable(ctx, x, unproc, free, Y)), None) or lead_lb(ctx, unproc, free, Y)

LEADERS = {'index': lead_index, 'lb': lead_lb, 'P': lead_P, 'P_lb': lead_P_lb}

def efx0(n, m, v, X):
    if X is None: return False
    B = [[g for g in range(m) if X[g] == i] for i in range(n)]
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in B[i])
        for j in range(n):
            if i == j or not B[j]: continue
            s = sum(v[i].get(g, 0) for g in B[j]); mn = min(v[i].get(g, 0) for g in B[j])
            if s - mn > own: return False
    return True
