"""Self-contained checker for round_e.py witnesses (k4/oc1max_multi.md §17), e.g.
results/k4_oc1max_multi/round_e_sel2_witnesses.json.gz.  Imports nothing from this workstream; every notion is recomputed
from the definitions (ties broken by good index).  Per start, with present agents A and deleted goods G (initially all
agents, no goods):
  1. the picks are the SD outcome of the witness order;
  2. for each round, at the current state (single goods for the agents of A, the SD outcome of the order restricted to
     A on the goods outside G):
     a. each settled k is dangerous there (some present agent wants its good; k values a junk good);
     b. its chain P is a prefix (length >= 2) of k's earliest-wanter chain (the order restricted to A), the chains are
        vertex-disjoint, and every agent on a chain strictly gains (an official chain move);
     c. T is inside (junk + the head's good) & R_k, is improving for k, and the T's are disjoint;
     d. the state after the round is as the witness says;
     e. (H): an agent of A - K that wanted a released head pick now values its good at least as much;
     f. SD-E(round): the new state of A - K is the SD outcome of the order restricted to A - K (goods outside G + T's);
     g. (L*): no T threatens any agent of A at its value after the round (the round's other members at v(T_k'));
     h. (P2)/(P3): no new T threatens an earlier settled agent at its v(T), and no released head pick is worth more to
        any settled agent than its v(T);
  3. the final allocation is complete, keeps every settled agent's T, extends the last state by junk only, gives at most
     one agent two or more junk goods, and is raw EFX0: v_i(X_i) >= v_i(X_j - g) for all i != j, g in X_j.
Negative tests (mutated witnesses) must be rejected.

    python3 k4/oc1max_multi/check_rounds.py WITNESSES.json.gz [EXPORT.json.gz]
"""
import sys, json, gzip, copy, hashlib


def check(st):
    sets, vals, picks, w = st['sets'], st['vals'], st['picks'], st['witness']
    if w is None: return 'no witness'
    n = len(sets); m = 1 + max(max(s) for s in sets if s)
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    V = lambda i, S: sum(v[i].get(g, 0) for g in S)
    rk = lambda i, g: (v[i][g], -g)
    thr = lambda i, t, S: len(S) >= 2 and max(V(i, [x for x in S if x != g]) for g in S) > t

    def sd(order, agents, banned):
        taken = set(banned); Y = {}
        for i in order:
            if i not in agents: continue
            av = [g for g in v[i] if g not in taken]
            if av: g = max(av, key=lambda h: rk(i, h)); Y[i] = g; taken.add(g)
            else: Y[i] = None
        return Y

    order = w['order']
    if sorted(order) != list(range(n)): return 'order'
    Y = sd(order, set(range(n)), set())
    if [Y[i] for i in range(n)] != list(picks): return '1 picks'
    A = set(range(n)); G = set(); cur = [[picks[i]] if picks[i] is not None else [] for i in range(n)]; tau = {}
    for rnd in w['rounds']:
        held = set(g for i in A for g in cur[i]); J = [g for g in range(m) if g not in held and g not in G]
        val = {i: V(i, cur[i]) for i in A}
        K = [s['k'] for s in rnd['settled']]
        if len(set(K)) != len(K) or not set(K) <= A: return '2 settled agents'
        pos = {a: t for t, a in enumerate(order)}
        used = set(); taken = set(); new = {i: list(cur[i]) for i in A}; rel = []
        for s in rnd['settled']:
            k, P, T = s['k'], s['P'], s['T']
            if len(cur[k]) != 1 or not any(i != k and v[i].get(cur[k][0], 0) > val[i] for i in A): return '2a k frozen'
            if not any(g in v[k] for g in J): return '2a k dangerous'
            E = [k]
            while True:
                ws = [i for i in A if i != E[-1] and len(cur[E[-1]]) == 1 and v[i].get(cur[E[-1]][0], 0) > val[i]]
                if not ws: break
                nxt = min(ws, key=lambda i: pos[i])
                if nxt in E: return '2b want-cycle (not an SD state)'      # hardening (referee): never loops
                E.append(nxt)
            if len(P) < 2 or P != E[:len(P)]: return '2b not an E(k) prefix'
            if used & set(P): return '2b chains not disjoint'
            used |= set(P); z = P[-1]
            if not set(T) <= set(J) | set(cur[z]) or not all(g in v[k] for g in T) or V(k, T) <= val[k]: return '2c T'
            if taken & set(T): return '2c T not disjoint'
            taken |= set(T); new[k] = sorted(T)
            for t in range(1, len(P)):
                new[P[t]] = list(cur[P[t - 1]])
                if V(P[t], new[P[t]]) <= val[P[t]]: return '2b chain agent does not gain'
            if cur[z][0] not in T: rel.append(cur[z][0])
        if [sorted(new.get(i, cur[i])) for i in range(n)] != [sorted(x) for x in rnd['state']]: return '2d state'
        nv = {i: V(i, new[i]) for i in A}
        for y in rel:
            if any(v[a].get(y, 0) > val[a] and v[a].get(y, 0) > nv[a] for a in A - set(K)): return '2e (H)'
        G2 = G | taken
        Y2 = sd(order, A - set(K), G2)
        if any(len(new[i]) != 1 or Y2[i] != new[i][0] for i in A - set(K)): return '2f SD-E(round)'
        tau2 = {k: V(k, new[k]) for k in K}
        for s in rnd['settled']:
            T = s['T']
            for i in A:
                if i == s['k']: continue
                if thr(i, tau2[i] if i in tau2 else nv[i], T): return '2g (L*)'
            for f in tau:
                if thr(f, tau[f], T): return '2h (P2)'
        tau.update(tau2)
        if any(v[f].get(y, 0) > tau[f] for y in rel for f in tau): return '2h (P3)'
        A -= set(K); G = G2; cur = [list(new.get(i, cur[i])) for i in range(n)]
    X = w['alloc']
    if sorted(g for x in X for g in x) != list(range(m)): return '3 not a complete allocation'
    held = set(g for i in range(n) for g in cur[i]); J = set(range(m)) - held
    extra = [set(X[i]) - set(cur[i]) for i in range(n)]
    if any(not set(cur[i]) <= set(X[i]) or not extra[i] <= J for i in range(n)): return '3 extends the last state by junk'
    if any(extra[f] for f in tau): return '3 a settled agent receives junk'
    if sum(1 for e in extra if len(e) >= 2) > 1: return '3 one absorber'
    for i in range(n):
        xi = V(i, X[i])
        for j in range(n):
            if i != j and any(V(i, [g for g in X[j] if g != r]) > xi for r in X[j]): return '3 EFX0'
    return 'ok'


def mutants(st):
    w = st['witness']
    if not w or not w['rounds']: return
    a = copy.deepcopy(st); a['witness']['order'] = a['witness']['order'][::-1]; yield 'order reversed', a
    a = copy.deepcopy(st); s0 = a['witness']['rounds'][0]['settled'][0]; s0['T'] = s0['T'][:1]; yield 'T cut to one good', a
    a = copy.deepcopy(st); x = a['witness']['alloc']; i = a['witness']['rounds'][0]['settled'][0]['k']; j = (i + 1) % len(x)
    x[i], x[j] = x[j], x[i]; yield 'bundles swapped', a
    a = copy.deepcopy(st); s0 = a['witness']['rounds'][0]['settled'][0]
    if len(s0['P']) > 2: s0['P'] = s0['P'][:1] + s0['P'][2:]; yield 'chain agent skipped', a


if __name__ == '__main__':
    d = json.load(gzip.open(sys.argv[1])); C = {}; neg = {}; nneg = 0
    for t, st in enumerate(d['starts']):
        r = check(st); C[r] = C.get(r, 0) + 1
        if t % 100 == 0:
            for name, a in mutants(st):
                if a == st: continue
                nneg += 1
                if check(a) == 'ok': neg[name] = neg.get(name, 0) + 1
    print('$ python3 k4/oc1max_multi/check_rounds.py', *sys.argv[1:])
    print('witness file sha256', hashlib.sha256(open(sys.argv[1], 'rb').read()).hexdigest())
    print('starts', len(d['starts']), 'results', C)
    print('negative tests', nneg, 'accepted (must be 0):', sum(neg.values()), neg)
    if len(sys.argv) > 2:      # the witness starts must be exactly the export's starts (as a multiset)
        import collections
        ex = sys.argv[2]; e = json.load(gzip.open(ex))
        key = lambda a, b, c: json.dumps([a, b, list(c)])
        X = collections.Counter(key(hg['sets'], s0['vals'], s0['picks']) for hg in e['hypergraphs'] for s0 in hg['starts'])
        Y = collections.Counter(key(st['sets'], st['vals'], st['picks']) for st in d['starts'])
        print('export sha256', hashlib.sha256(open(ex, 'rb').read()).hexdigest(), 'starts', sum(X.values()),
              '| export starts without a witness entry:', sum((X - Y).values()), '| witness starts outside the export:', sum((Y - X).values()))
