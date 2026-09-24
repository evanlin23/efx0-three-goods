"""Brute-force checks of the reduction lemmas for EFX0 with agents having <= 3 relevant goods (additive)."""
import itertools, random

def efx0(n, v, X):
    """X: owner of each good. EFX0: for all i != j, g in X_j: v_i(X_j - g) <= v_i(X_i)."""
    B = [[] for _ in range(n)]
    for g, o in enumerate(X): B[o].append(g)
    for i in range(n):
        own = sum(v[i][g] for g in B[i])
        for j in range(n):
            if i == j or len(B[j]) <= 1: continue
            vals = [v[i][g] for g in B[j]]
            if sum(vals) - min(vals) > own: return False
    return True

def brute(agents, goods, v):
    """any EFX0 allocation of `goods` among `agents` (restricted instance), or None"""
    k = len(agents)
    for Y in itertools.product(range(k), repeat=len(goods)):
        B = [[] for _ in range(k)]
        for idx, o in enumerate(Y): B[o].append(goods[idx])
        ok = True
        for a in range(k):
            i = agents[a]; own = sum(v[i][g] for g in B[a])
            for b in range(k):
                if a == b or len(B[b]) <= 1: continue
                vals = [v[i][g] for g in B[b]]
                if sum(vals) - min(vals) > own: ok = False; break
            if not ok: break
        if ok: return {goods[idx]: agents[o] for idx, o in enumerate(Y)}
    return None

def peel_step(agents, goods, v, rng):
    """return (agent, bundle) for some peelable agent (random choice among peelable), or None.
       R1: <=2 remaining relevant goods, or top-heavy  -> take top good alone (or nothing if no relevant goods)
       R2: >=2 goods relevant only to this agent (among remaining agents) -> take all its private goods"""
    R = {i: [g for g in goods if v[i][g] > 0] for i in agents}
    deg = {g: sum(1 for i in agents if g in R[i]) for g in goods}
    cands = []
    for i in agents:
        Ri = sorted(R[i], key=lambda g: -v[i][g])
        if not Ri: cands.append((i, [])); continue
        if len(Ri) <= 2 or v[i][Ri[0]] >= sum(v[i][g] for g in Ri[1:]):
            cands.append((i, [Ri[0]])); continue
        priv = [g for g in Ri if deg[g] == 1]
        if len(priv) >= 2 and sum(v[i][g] for g in priv) >= sum(v[i][g] for g in Ri if g not in priv):
            cands.append((i, priv))
    return rng.choice(cands) if cands else None

def pipeline(n, m, v, rng):
    agents, goods, X = list(range(n)), list(range(m)), [None] * m
    while len(agents) >= 2:
        st = peel_step(agents, goods, v, rng)
        if st is None: break
        i, P = st
        for g in P: X[g] = i
        goods = [g for g in goods if g not in P]; agents.remove(i)
    if len(agents) == 1:
        for g in goods: X[g] = agents[0]
        return X, None
    rel = sorted(set(g for i in agents for g in goods if v[i][g] > 0))
    junk = [g for g in goods if g not in rel]
    core = (tuple(agents), tuple(rel))
    Y = brute(agents, rel, v)
    if Y is None: return None, core
    own = {i: [g for g in rel if Y[g] == i] for i in agents}
    val = lambda i, S: sum(v[i][g] for g in S)
    while True:                                   # envy-cycle elimination on the core
        env = {i: [j for j in agents if j != i and val(i, own[j]) > val(i, own[i])] for i in agents}
        cyc, seen, path = None, set(), []
        def dfs(u, stack):
            nonlocal cyc
            if cyc: return
            if u in stack: cyc = stack[stack.index(u):]; return
            if u in seen: return
            seen.add(u)
            for w in env[u]: dfs(w, stack + [u])
        for s0 in agents:
            dfs(s0, [])
            if cyc: break
        if not cyc: break
        new = {cyc[k]: own[cyc[(k + 1) % len(cyc)]] for k in range(len(cyc))}   # each takes the bundle it envies
        own.update(new)
    src = [j for j in agents if not any(j in env[i] for i in agents)][0]
    for i in agents:
        for g in own[i]: X[g] = i
    for g in junk: X[g] = src
    return X, core

def rand_inst(rng):
    n = rng.choice([3, 4, 4, 5]); m = rng.randint(n + 1, 8 if n < 5 else 7)
    v = [[0] * m for _ in range(n)]
    pool = rng.sample(range(m), min(m, rng.choice([4, 5, 6, m])))
    for i in range(n):
        k = rng.choice([3, 3, 3, 2, 1])
        for g in rng.sample(pool if rng.random() < .8 else range(m), k):
            v[i][g] = rng.randint(4, 9) if rng.random() < .85 else rng.randint(1, 20)
    return n, m, v

if __name__ == '__main__':
  rng = random.Random(7)
  fails = cores = 0; N = 1500
  for t in range(N):
      n, m, v = rand_inst(rng)
      X, core = pipeline(n, m, v, rng)
      if core: cores += 1
      if X is None or not efx0(n, v, X): fails += 1; print("FAIL", n, m, v, X)
  print(f"[pipeline R1+R2 peeling, junk-to-source] instances={N} reaching a nontrivial core={cores} failures={fails}")
