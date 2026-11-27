"""Coordinator's independent replay (2026-11-26) of the OC1 counterexample on a strict connected k = 4 core: the strict
perturbations B< and B> of instance 36 of the TTC session's list, as reported by the k4-oc1-hall session
(k4/oc1_hall.md §16).  Own code, raw definitions, no SAT, nothing imported from the repository.

Core check, written from the K4.CORE row of LEDGER.md: (C1) 3 <= |R_i| <= 4; (C2) 2 v_i(g) < v_i(R_i) for every g;
(C3) |P_i| + 2 <= |R_i|; (C4) |P_i| = 2 => v_i(P_i) < v_i(S_i); (C5) every good relevant to someone; strict
(disjoint nonempty subsets of R_i have different values); connected (agents linked through shared goods).

OC1 (k4/sdc.md §29), official move rule: improving chains x0..xt with disjoint junk sets H inside the receivers'
relevant goods; t = 0: x0 adds junk H0; t >= 1: x0 takes H0 (from J and B_{xt}), x_i takes B_{x_{i-1}} + H_i (H_i from
J), every mover strictly gains, a chain never hands on an empty base; rings w0 -> ... -> w0, each takes its
predecessor's (nonempty) base plus junk, all strictly gain.  No caps on set sizes.  One-absorber completion: junk goes
out with at most one agent receiving two or more junk goods, and the result is EFX0 (removing any good, including a
good of value 0 to the envier).

    python3 k4/sdc/oc1_core_cex_verify.py B< | B> [orders]"""
import itertools, sys, collections, multiprocessing as mp

SETS = [[0, 2, 3, 1], [6, 4, 5, 9], [1, 2, 3, 9], [1, 6, 7, 8], [3, 6, 9], [1, 3, 6, 9]]
VALS = {'B<': [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 21], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]],
        'B>': [[6, 14, 16, 12], [4, 18, 12, 28], [28, 4, 16, 19], [16, 14, 12, 6], [28, 8, 24], [20, 30, 8, 4]]}
NAME = sys.argv[1]
sets, vals = SETS, VALS[NAME]
n = len(sets); m = 1 + max(max(s) for s in sets)
v = [dict(zip(s, x)) for s, x in zip(sets, vals)]
R = [set(s) for s in sets]
V = lambda i, S: sum(v[i].get(g, 0) for g in S)


def core_failures():
    f = []
    for i in range(n):
        d = len(R[i]); tot = V(i, R[i])
        if not 3 <= d <= 4: f.append('C1 agent %d' % i)
        if any(2 * v[i][g] >= tot for g in R[i]): f.append('C2 agent %d' % i)
        P = [g for g in R[i] if all(g not in R[j] for j in range(n) if j != i)]
        S = [g for g in R[i] if g not in P]
        if len(P) + 2 > d: f.append('C3 agent %d' % i)
        if len(P) == 2 and not V(i, P) < V(i, S): f.append('C4 agent %d' % i)
        sums = collections.defaultdict(list)
        for r in range(1, d + 1):
            for T in itertools.combinations(sorted(R[i]), r): sums[V(i, T)].append(set(T))
        for T in sums.values():
            if any(not (a & b) for a, b in itertools.combinations(T, 2)): f.append('tie agent %d' % i); break
    if set().union(*R) != set(range(m)): f.append('C5')
    comp = {0}; grow = True
    while grow:
        grow = False
        for j in range(n):
            if j not in comp and any(R[j] & R[i] for i in comp): comp.add(j); grow = True
    if len(comp) < n: f.append('disconnected')
    return f


def privates():
    return {i: sorted(g for g in R[i] if all(g not in R[j] for j in range(n) if j != i)) for i in range(n)}


def sd(order):
    taken = set(); picks = [None] * n
    for i in order:
        av = [g for g in R[i] if g not in taken]
        if av:
            g = max(av, key=lambda g: v[i][g]); picks[i] = g; taken.add(g)
    return tuple(picks)


def efx0(B):
    for i in range(n):
        own = V(i, B[i])
        for j in range(n):
            if j != i and B[j]:
                if V(i, B[j]) - min(v[i].get(h, 0) for h in B[j]) > own: return False
    return True


def one_absorber(base):
    """is there a junk placement with at most one agent receiving >= 2 junk goods, giving an EFX0 allocation?"""
    J = [g for g in range(m) if all(g not in b for b in base)]
    for a in [None] + list(range(n)):
        for r in range(0 if a is None else 2, len(J) + 1):
            if a is None and r: break
            for S in itertools.combinations(J, r):
                rest = [g for g in J if g not in S]
                others = [i for i in range(n) if i != a]
                for recv in itertools.permutations(others, len(rest)):
                    B = [list(b) for b in base]
                    if a is not None: B[a] += list(S)
                    for g, i in zip(rest, recv): B[i].append(g)
                    if efx0(B): return True
    return False


def subsets(xs):
    for r in range(len(xs) + 1): yield from itertools.combinations(xs, r)


def moves(base):
    J = [g for g in range(m) if all(g not in b for b in base)]
    res = set()
    key = lambda nb: tuple(tuple(sorted(b)) for b in nb)
    for x in range(n):
        for H in subsets([g for g in J if g in R[x]]):
            if H and V(x, H) > 0:
                nb = [list(b) for b in base]; nb[x] = list(base[x]) + list(H); res.add(key(nb))

    def ext(path, used, assign):
        xt = path[-1]
        if len(path) >= 2:
            pool = [g for g in J if g not in used and g in R[path[0]]] + [g for g in base[xt] if g in R[path[0]]]
            for H0 in subsets(pool):
                if H0 and V(path[0], H0) > V(path[0], base[path[0]]):
                    nb = [list(b) for b in base]; nb[path[0]] = list(H0)
                    for i in range(1, len(path)): nb[path[i]] = list(base[path[i - 1]]) + list(assign[i])
                    res.add(key(nb))
        if len(path) >= n or not base[xt]: return
        for y in range(n):
            if y in path: continue
            for H in subsets([g for g in J if g not in used and g in R[y]]):
                if V(y, list(base[xt]) + list(H)) > V(y, base[y]):
                    ext(path + [y], used | set(H), {**assign, len(path): H})
    for x in range(n): ext([x], frozenset(), {})
    for r in range(2, n + 1):
        for cyc in itertools.permutations(range(n), r):
            if cyc[0] != min(cyc): continue

            def ring(i, used, assign):
                if i == r:
                    nb = [list(b) for b in base]
                    for t in range(r): nb[cyc[t]] = list(base[cyc[t - 1]]) + list(assign[t])
                    res.add(key(nb)); return
                w, pred = cyc[i], cyc[i - 1]
                if not base[pred]: return
                for H in subsets([g for g in J if g not in used and g in R[w]]):
                    if V(w, list(base[pred]) + list(H)) > V(w, base[w]): ring(i + 1, used | set(H), {**assign, i: H})
            ring(0, frozenset(), {})
    return res


def check(picks):
    base = [[p] if p is not None else [] for p in picks]
    if one_absorber(base): return 'picks complete', 0
    M = moves(base)
    for st in M:
        if one_absorber([list(b) for b in st]): return 'one move repairs', len(M)
    return 'OC1 fails', len(M)


if __name__ == '__main__':
    print('$ python3 k4/sdc/oc1_core_cex_verify.py', *sys.argv[1:])
    print(NAME, 'sets', sets, 'vals', vals, 'm', m)
    print('core failures:', core_failures() or 'none (strict connected k = 4 core)')
    print('private goods:', privates())
    p = sd(list(range(n)))
    res, nm = check(p)
    print('order 0..5: picks', p, '| moves', nm, '|', res)
    if 'orders' in sys.argv:
        orders = list(itertools.permutations(range(n)))
        picks = collections.Counter(sd(o) for o in orders)
        with mp.Pool(mp.cpu_count()) as pool:
            out = dict(zip(picks, pool.map(check, list(picks))))
        C = collections.Counter()
        for pk, c in picks.items(): C[out[pk][0]] += c
        print('distinct pick vectors', len(picks), '| orders:', dict(C))
        for pk in picks:
            if out[pk][0] == 'OC1 fails': print('  fails: picks', pk, 'orders', picks[pk], 'moves', out[pk][1])
