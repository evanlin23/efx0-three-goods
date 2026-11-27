"""Self-contained checker for the Theorem REC-S witnesses (k4/oc1max_multi.md §12), e.g.
results/k4_oc1max_multi/recs_witnesses_n4.json.gz.  It imports nothing from this workstream: every notion is
recomputed from the definitions (ties broken by good index, as in k4/sdc).  Per start it checks:
  1. the picks are the serial-dictatorship outcome of the witness order;
  2. k is dangerous (frozen: some agent wants its pick; values a junk good);
  3. P1 is the earliest-wanter chain E(k) of that order, ending at an agent nobody wants;
  4. T: two goods of (junk + head's pick), valued by k, with v_k(T) > p_k; move 1 (k takes T, x_i takes x_{i-1}'s pick)
     is an official chain: every agent on it strictly gains;
  5. (L): every other agent with a relevant good values each good of T strictly below its value after move 1;
  6. Lemma SD-E: after move 1, without k and T, the state is the SD outcome of the order minus k;
  7. move 2 = P2 from the state after move 1, not touching k: x_i takes its predecessor's single good and strictly
     gains, its first agent k' is dangerous there (without k and T), takes H0_2 inside junk + the head's good, gains;
     the head of P2 holds a good nobody wants;
  8. Theorem S's shape: k' ends with exactly (junk after move 1 + the head's old good) minus h, and h goes to one
     other agent;
  9. the final allocation X is a complete allocation extending the state after move 2 by junk only, with at most one
     agent receiving two or more junk goods (one-absorber), X_k = T, and raw EFX0: v_i(X_i) >= v_i(X_j - g) for all
     i != j and every g in X_j (zero-valued goods included).
Negative tests (mutated witnesses) must all be rejected.

    python3 k4/oc1max_multi/check_recs.py WITNESSES.json.gz
"""
import sys, json, gzip, copy


def check(st):
    sets, vals, picks, w = st['sets'], st['vals'], st['picks'], st['witness']
    if w is None: return 'no witness'
    n = len(sets); m = 1 + max(max(s) for s in sets if s)
    v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
    V = lambda i, S: sum(v[i].get(g, 0) for g in S)
    rk = lambda i, g: (v[i][g], -g)

    def sd(order, agents, banned):
        taken = set(banned); Y = {}
        for i in order:
            if i not in agents: continue
            av = [g for g in v[i] if g not in taken]
            if av:
                g = max(av, key=lambda h: rk(i, h)); Y[i] = g; taken.add(g)
            else: Y[i] = None
        return Y

    order = w['order']
    if sorted(order) != list(range(n)): return 'order'
    Y = sd(order, set(range(n)), set())
    if [Y[i] for i in range(n)] != list(picks): return '1 picks'
    J = [g for g in range(m) if g not in set(picks)]
    p = [V(i, [picks[i]]) if picks[i] is not None else 0 for i in range(n)]
    wants = lambda i, g, t: v[i].get(g, 0) > t
    k = w['k']
    if picks[k] is None or not any(wants(i, picks[k], p[i]) for i in range(n) if i != k): return '2 k frozen'
    if not any(g in v[k] for g in J): return '2 k dangerous'
    pos = {a: t for t, a in enumerate(order)}; P = [k]
    while True:
        ws = [i for i in range(n) if i != P[-1] and wants(i, picks[P[-1]], p[i])]
        if not ws: break
        P.append(min(ws, key=lambda i: pos[i]))
    if P != w['P1'] or len(P) < 2: return '3 E(k)'
    z = P[-1]; T = w['T']
    if len(set(T)) != 2 or not set(T) <= set(J) | {picks[z]} or not all(g in v[k] for g in T): return '4 T'
    if V(k, T) <= p[k]: return '4 k gains'
    B1 = [[picks[i]] if picks[i] is not None else [] for i in range(n)]; B1[k] = sorted(T)
    for t in range(1, len(P)):
        B1[P[t]] = [picks[P[t - 1]]]
        if V(P[t], B1[P[t]]) <= p[P[t]]: return '4 chain gains'
    b1 = [V(i, B1[i]) for i in range(n)]
    if any(i != k and v[i] and any(v[i].get(g, 0) >= b1[i] for g in T) for i in range(n)): return '5 (L)'
    rest = set(range(n)) - {k}
    Y1 = sd([a for a in order if a != k], rest, set(T))
    if any(Y1[i] != (B1[i][0] if B1[i] else None) or len(B1[i]) > 1 for i in rest): return '6 SD-E'
    held1 = set(g for i in range(n) for g in B1[i]); J1 = [g for g in range(m) if g not in held1]
    P2, H0 = w['P2'], w['H0_2']
    if len(P2) < 2 or len(set(P2)) != len(P2) or k in P2: return '7 P2 agents'
    k2, z2 = P2[0], P2[-1]
    if len(B1[k2]) != 1 or not any(wants(i, B1[k2][0], b1[i]) for i in rest if i != k2): return '7 k2 frozen'
    if not any(g in v[k2] for g in J1): return '7 k2 dangerous'
    if any(wants(i, B1[z2][0], b1[i]) for i in rest if i != z2): return '7 head unwanted'
    if not set(H0) <= set(J1) | set(B1[z2]) or V(k2, H0) <= b1[k2]: return '7 k2 takes H0'
    B2 = copy.deepcopy(B1); B2[k2] = sorted(H0)
    for t in range(1, len(P2)):
        if len(B1[P2[t - 1]]) != 1: return '7 single goods'
        B2[P2[t]] = list(B1[P2[t - 1]])
        if V(P2[t], B2[P2[t]]) <= b1[P2[t]]: return '7 chain gains'
    X, h = w['X'], w['h']
    if sorted(g for x in X for g in x) != list(range(m)): return '9 not a complete allocation'
    held2 = set(g for i in range(n) for g in B2[i]); J2 = set(range(m)) - held2
    extra = [set(X[i]) - set(B2[i]) for i in range(n)]
    if any(not set(B2[i]) <= set(X[i]) or not extra[i] <= J2 for i in range(n)): return '9 extends move 2 by junk'
    if sum(1 for e in extra if len(e) >= 2) > 1: return '9 one absorber'
    if sorted(X[k]) != sorted(T): return '9 X_k = T'
    if sorted(X[k2]) != sorted((set(J1) | set(B1[z2])) - {h}): return "8 owner's bundle W"
    if sum(1 for i in range(n) if i != k2 and h in X[i]) != 1 or any(len(extra[i]) > 1 for i in range(n) if i != k2):
        return '8 h to one other agent'
    for i in range(n):
        xi = V(i, X[i])
        for j in range(n):
            if i != j and any(V(i, [g for g in X[j] if g != r]) > xi for r in X[j]): return '9 EFX0'
    return 'ok'


def mutants(st):
    w = st['witness']
    if not w: return
    a = copy.deepcopy(st); a['witness']['X'][a['witness']['k']] = a['witness']['X'][a['witness']['k']][:1]; yield 'X_k cut', a
    a = copy.deepcopy(st); a['witness']['order'] = a['witness']['order'][::-1]; yield 'order reversed', a
    a = copy.deepcopy(st); a['witness']['P1'] = a['witness']['P1'][:1] + a['witness']['P1'][1:][::-1]; yield 'P1 permuted', a
    a = copy.deepcopy(st); x = a['witness']['X']; i = a['witness']['k']; j = (i + 1) % len(x)
    x[i], x[j] = x[j], x[i]; yield 'bundles of k swapped', a


if __name__ == '__main__':
    d = json.load(gzip.open(sys.argv[1])); C = {}; neg = {}; nneg = 0
    for t, st in enumerate(d['starts']):
        r = check(st); C[r] = C.get(r, 0) + 1
        if t % 50 == 0:
            for name, a in mutants(st):
                if a == st: continue                       # the mutation changed nothing (e.g. a chain of length 2)
                nneg += 1; rr = check(a)
                if rr == 'ok': neg[name] = neg.get(name, 0) + 1
    strict = sum(1 for st in d['starts'] if all(len(set(x)) == len(x) for x in st['vals']))
    print('$ python3 k4/oc1max_multi/check_recs.py', *sys.argv[1:])
    print('starts', len(d['starts']), 'results', C)
    print('starts with strict values (distinct per agent):', strict)
    print('negative tests', nneg, 'accepted (must be 0):', sum(neg.values()), neg)
