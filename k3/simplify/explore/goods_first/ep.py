"""EP ("envy the pool"): the best candidate of the goods-first / envy-graph exploration. Evidence only, no proof.

Input: n agents, m goods, additive v[i] = {good: positive value}, at most three goods per agent.
State: bundles X_1..X_n and the pool P of unallocated goods (initially X_i = {} and P = all goods).
"i envies a set S" means v_i(S) > v_i(X_i). Cycle rotation (F2): while the envy graph among the bundles has a cycle,
each agent on it takes the next one's bundle. Rotation is applied before every step.

  1. Draft and swaps. Repeat while some agent envies P:
     (a) if some agent with an empty bundle envies P: the first such agent that can be peeled (its favourite pool good
         is worth at least its other pool goods together), else the first such agent, takes its favourite pool good;
     (b) else, if some agent envies a single pool good: the first such agent takes its favourite pool good and puts
         its old bundle back into P;
     (c) else the first agent i that envies P takes the shortest prefix of its ranking (restricted to P) that it
         envies, and puts its old bundle back into P. (With three goods: an agent holding only its top a takes b
         and c.)
     Every step keeps EFX0: the set taken is a minimal envied set (nobody envies it minus one good), as in the
     "little charity" algorithm of Chaudhury, Kavitha, Mehlhorn and Sgouritsa [unverified here]; the sum of the
     values strictly increases, so the loop ends.
  2. Placement. Repeat while P is non-empty:
     (a) if some agent values a pool good g and taking it keeps EFX0, the agent with g best ranked does so
         (ties: smallest agent, then smallest good);
     (b) else the smallest pool good goes to the first source of the envy graph for which EFX0 is kept
         (if none: to any agent for which it is kept; if none at all, the run FAILS and gives it to a source).

place='onesource' (the candidate of NOTES.md) replaces 2(b) by: a source of the envy graph that can take ALL of P
keeping EFX0 takes it (the first such source; if none, the run FAILS). Results and ablations: NOTES.md.
"""
from common import ranking, bval, threat, eliminate_cycles, sources, to_X

def keeps(n, v, B, s, g):
    nb = B[s] + [g]
    return all(bval(v[i], B[i]) >= threat(v[i], nb) for i in range(n) if i != s)

def ep(n, m, v, info=None, place='greedy', peel=True, absorber='search', up='any', src='source', rot=True):
    """place: 'greedy' (step 2 as in the docstring), 'onesource' (2(a), then ONE source takes all remaining goods),
    'sources' (no 2(a)). peel=False: step 1(a) ignores peelability (first empty-handed envier).
    absorber (onesource only): 'search' (first source that keeps EFX0), 'first' / 'last' (that source, no check),
    'recent' (the source whose bundle was formed or grew last), 'recent_e' (an empty-handed source, else 'recent'), 'r_like' (K3S's r: a source that took nothing in 2(a),
    latest phase-1 bundle).
    up: 'any' (2(a) as stated), 'bc' (2(a) only for an agent holding exactly its second good, taking its third),
    'none' (no 2(a)). src='any': in 2(b) the first agent (not only a source) for which EFX0 is kept.
    rot=False: never rotate envy cycles (sources are taken in the envy graph as it is; if none, any agent)."""
    if not rot:
        from common import envy as _envy
        elim = lambda n, v, B: _envy(n, v, B)
    else:
        elim = eliminate_cycles
    rk = ranking(v); pos = [{g: t for t, g in enumerate(rk[i])} for i in range(n)]
    B = [[] for _ in range(n)]; P = set(range(m)); steps = {'a': 0, 'b': 0, 'c': 0, 'up': 0, 'placed': 0, 'nonsource': 0}; recv = set()
    stamp = {}; clock = [0]          # bundle (list object) -> time it was formed or last grew; moves with rotations
    def mark(i): clock[0] += 1; stamp[id(B[i])] = clock[0]
    stamp1 = {}; grew = set()        # phase-1 stamps (bundle -> time formed), agents that took a good in 2(a)
    use_peel = peel
    def peel(i):
        fr = [v[i][g] for g in rk[i] if g in P]
        return not fr or fr[0] >= sum(fr[1:])
    while True:
        elim(n, v, B)
        env = [i for i in range(n) if bval(v[i], P) > bval(v[i], B[i])]
        if not env: break
        emp = [i for i in env if not B[i]]
        if emp:
            i = next((i for i in emp if peel(i)), emp[0]) if use_peel else emp[0]
            g = next(g for g in rk[i] if g in P); B[i] = [g]; P.discard(g); mark(i); steps['a'] += 1; continue
        one = [i for i in env if any(v[i].get(g, 0) > bval(v[i], B[i]) for g in P)]
        if one:
            i = one[0]; g = next(g for g in rk[i] if g in P)
            P |= set(B[i]); P.discard(g); B[i] = [g]; mark(i); steps['b'] += 1; continue
        i = env[0]; Z = [g for g in rk[i] if g in P]
        Z = next(Z[:t] for t in range(1, len(Z) + 1) if bval(v[i], Z[:t]) > bval(v[i], B[i]))
        P |= set(B[i]); P -= set(Z); B[i] = list(Z); mark(i); steps['c'] += 1
    stamp1 = dict(stamp)
    failed = False
    while P:
        E = elim(n, v, B); S = sources(n, E) or list(range(n))
        if src == 'any': S = list(range(n))
        if place == 'sources' or up == 'none': cand = []
        elif up == 'bc':
            cand = [(1, s, rk[s][2]) for s in range(n) if len(rk[s]) == 3 and B[s] == [rk[s][1]]
                    and rk[s][2] in P and keeps(n, v, B, s, rk[s][2])]
        else:
            cand = [(pos[s][g], s, g) for g in P for s in range(n) if g in v[s] and keeps(n, v, B, s, g)]
        if cand:
            _, s, g = min(cand); B[s].append(g); P.discard(g); mark(s); grew.add(s); steps['up'] += 1; continue
        if place == 'onesource':
            # one absorber: a source takes all remaining pool goods at once
            def keeps_all(s):
                nb = B[s] + sorted(P)
                return all(bval(v[i], B[i]) >= threat(v[i], nb) for i in range(n) if i != s)
            if absorber == 'search':
                s = next((s for s in S if keeps_all(s)), None)
                if info is not None: info['first_source_ok'] = keeps_all(S[0])
                if s is None: s = S[0]; failed = True
            elif absorber == 'recent':
                s = max(S, key=lambda s: stamp.get(id(B[s]), -1))
            elif absorber == 'r_like':
                s = max(S, key=lambda s: (s not in grew, stamp1.get(id(B[s]), stamp.get(id(B[s]), -1))))
            elif absorber == 'recent_e':
                s = max(S, key=lambda s: (not B[s], stamp.get(id(B[s]), -1)))
            else:
                s = S[0] if absorber == 'first' else S[-1]
            B[s] += sorted(P); P = set(); break
        g = min(P)
        s = next((s for s in S if keeps(n, v, B, s, g)), None)
        if s is None:
            s = next((s for s in range(n) if keeps(n, v, B, s, g)), None); steps['nonsource'] += s is not None
        if s is None: s = S[0]; failed = True
        B[s].append(g); P.discard(g); steps['placed'] += 1; recv.add(s)
    elim(n, v, B)
    if info is not None: info.update(steps); info['failed'] = failed; info['receivers'] = len(recv)
    return to_X(m, B)
