"""Step 0 computer checks (proof/step0-lemmas): corroboration of the hand proofs in proofs/lemmas.md and
proofs/counterexamples.md. Every check decides EFX0 with the raw definition (for all i != j and g in X_j,
v_i(X_i) >= v_i(X_j - g)) on exact integer values; nothing here imports frontier.py or the L5 model code.
  L5   one balanced agent in every local configuration its safety can depend on (4 agents; its 3 relevant goods plus 3
       goods worthless to it: all 4^6 allocations), all balanced integer realizations with a <= 12: the cases
       T/P/B/C/E agree with the raw definition; with ties they remain sufficient (not necessary).
  L2   R1/R2 peeling, exhaustive on two small grids (n = 3, m = 4, values in {0, 1, 2}; n = 2, m = 4, values in
       {0, ..., 3}; all instances with |R_i| <= 3): peel + ANY EFX0 allocation of the rest is EFX0.
  L3   junk, exhaustive on the same grids: envy-cycle elimination keeps EFX0; junk to a source is EFX0.
  L8   the beta = 1 core (m = 2n; genbg finds exactly one per n) with the orientation allocation, every ranking.
  L4, L7, L11  identities and kernel shapes on every connected core genbg enumerates (n <= 6 all m; n = 7, m >= 11).
  L9   agrees with the raw definition on every size-<=2 allocation of the X2 hypergraph.
  X2   the n = 6 example: the stated allocation is EFX0; none of the 4,082,400 allocations with bundles <= 2 is
       (and the same brute force does find such allocations for a neighbouring profile, so it is not vacuous).
  X3   four identical agents + three worthless goods: EFX0 allocations exist, and each has a bundle of >= 3 goods.
  D    tools/check_certs.py checks EFX0 coverage but not the shape conjecture D asks for: here every allocation stored
       in results/certs_*.json.gz is checked to have at most one bundle of more than two goods.
Usage: python step0_checks.py [CHECK ...]   (all checks: about 3 minutes on one CPU; CHECK in L5 L2 L8 L11 X2 X3 D;
exit status 1 if any check fails)"""
import itertools, sys, time, collections
import networkx as nx
from cores_nauty import gen_cores_nauty

FAIL = []
def report(name, ok, msg):
    print(f"[{'OK' if ok else 'FAIL'}] {name}: {msg}", flush=True)
    if not ok: FAIL.append(name)

def value(vi, S): return sum(vi.get(g, 0) for g in S)

def safe(v, bundles, i):
    """Raw EFX0 for agent i: v_i(X_i) >= v_i(X_j - g) for every j != i and g in X_j."""
    own = value(v[i], bundles[i])
    for j, B in enumerate(bundles):
        if j != i and B:
            tot = value(v[i], B)
            if any(tot - v[i].get(g, 0) > own for g in B): return False
    return True

def efx0(v, bundles): return all(safe(v, bundles, i) for i in range(len(v)))

def bundles_of(X, n): return [[g for g, o in enumerate(X) if o == j] for j in range(n)]

BAL = [(a, b, c) for a in range(1, 13) for b in range(1, a) for c in range(1, b) if a < b + c]   # strict, balanced
TIED = [(a, b, c) for a in range(1, 9) for b in range(1, a + 1) for c in range(1, b + 1)
        if a < b + c and (a == b or b == c)]                                                      # balanced with ties

# ---------------------------------------------------------------------------------------------------- L5
def cases(a, b, c, bundles, i):
    where = {g: k for k, B in enumerate(bundles) for g in B}
    size = lambda g: len(bundles[where[g]])
    alone = lambda g: size(g) == 1
    holds = lambda g: where[g] == i
    T = holds(a) and (holds(b) or holds(c) or not (where[b] == where[c] and size(b) >= 3))
    return T or (holds(b) and holds(c)) or (holds(b) and alone(a)) or (holds(c) and alone(a) and alone(b)) \
        or (alone(a) and alone(b) and alone(c))

def check_L5():
    t0 = time.time()
    order_ok = all(sorted(range(8), key=lambda s: sum(t for k, t in enumerate((a, b, c)) if s >> k & 1))
                   == [0, 4, 2, 1, 6, 5, 3, 7] for a, b, c in BAL)   # 0 < c < b < a < b+c < a+c < a+b < a+b+c
    report("L5 order", order_ok, f"subset sums of all {len(BAL)} strict balanced triples with a <= 12 are ordered "
           "0 < c < b < a < b+c < a+c < a+b < a+b+c")
    configs, mism, insuff, notnec = set(), 0, 0, 0
    allocs = list(itertools.product(range(4), repeat=6))                 # agent 0 values goods 0, 1, 2; 3, 4, 5 junk
    for perm in itertools.permutations(range(3)):                        # (a, b, c) = goods perm[0], perm[1], perm[2]
        a, b, c = perm
        for X in allocs:
            B = bundles_of(X, 4)
            pred = cases(a, b, c, B, 0)
            # the local configuration: what agent 0 holds, and for each other bundle meeting {0,1,2} that
            # intersection plus whether the bundle has other goods
            loc = (frozenset(g for g in B[0] if g < 3),
                   frozenset((frozenset(g for g in S if g < 3), len(S) > sum(g < 3 for g in S))
                             for S in B[1:] if any(g < 3 for g in S)))
            configs.add((perm, loc))
            for t in BAL:
                v = [{a: t[0], b: t[1], c: t[2]}] + [{}] * 3
                if safe(v, B, 0) != pred: mism += 1
            for t in TIED:
                v = [{a: t[0], b: t[1], c: t[2]}] + [{}] * 3
                r = safe(v, B, 0)
                if pred and not r: insuff += 1
                if r and not pred: notnec += 1
    per_perm = len(configs) // 6
    report("L5 cases", mism == 0, f"{len(allocs)} allocations x 6 rankings x {len(BAL)} strict realizations, "
           f"{per_perm} distinct local configurations per ranking: {mism} mismatches with the raw definition")
    report("L5 ties", insuff == 0, f"{len(TIED)} tied balanced realizations: cases hold but raw unsafe {insuff} times "
           f"(sufficiency); raw safe but no case {notnec} times (necessity fails with ties, as expected)  "
           f"[{time.time() - t0:.0f}s]")
    # every local configuration occurs: agent 0 holds any subset S of {0,1,2}; the rest is split into blocks, each
    # with or without extra goods. Count them: sum over S of sum over set partitions of the rest of 2^(#blocks).
    def count_rest(k):
        tot = 0
        for p in set_partitions(list(range(k))): tot += 2 ** len(p)
        return tot
    expected = sum(count_rest(3 - len(S)) for r in range(4) for S in itertools.combinations(range(3), r))
    report("L5 coverage", per_perm == expected, f"local configurations realized: {per_perm}, possible: {expected}")

def set_partitions(items):
    if not items: yield []; return
    first, rest = items[0], items[1:]
    for p in set_partitions(rest):
        yield [[first]] + p
        for k in range(len(p)): yield p[:k] + [[first] + p[k]] + p[k + 1:]

# ---------------------------------------------------------------------------------------------------- L2, L3
def all_efx0(agents, goods, v):
    """All EFX0 allocations (dict good -> agent) of `goods` among `agents` (sub-instance)."""
    out = []
    for Y in itertools.product(agents, repeat=len(goods)):
        B = [[g for g, o in zip(goods, Y) if o == a] for a in agents]
        if all(safe([v[a] for a in agents], B, k) for k in range(len(agents))): out.append(dict(zip(goods, Y)))
    return out

def peel_rules(i, agents, goods, v):
    """Bundles P that L2 allows agent i to take: R1 and R2 (R_i restricted to the remaining goods)."""
    R = sorted((g for g in goods if v[i].get(g, 0) > 0), key=lambda g: -v[i][g])
    out = []
    if not R: out.append(('R1', []))
    elif v[i][R[0]] >= value(v[i], R[1:]): out.append(('R1', [R[0]]))
    P = [g for g in R if all(v[j].get(g, 0) == 0 for j in agents if j != i)]
    if len(P) >= 2 and value(v[i], P) >= value(v[i], [g for g in R if g not in P]): out.append(('R2', P))
    return out

def instances(n, m, vals):
    for flat in itertools.product(vals, repeat=n * m):
        v = [{g: flat[i * m + g] for g in range(m) if flat[i * m + g] > 0} for i in range(n)]
        if all(len(vi) <= 3 for vi in v): yield v

def check_L2_L3(n=3, m=4, vals=(0, 1, 2)):
    t0 = time.time(); tried = collections.Counter(); bad = 0; junk_tried = rot = junk_bad = 0
    for v in instances(n, m, vals):
        agents, goods = list(range(n)), list(range(m))
        for i in agents:
            for rule, P in peel_rules(i, agents, goods, v):
                rest_a, rest_g = [a for a in agents if a != i], [g for g in goods if g not in P]
                for Y in all_efx0(rest_a, rest_g, v):
                    Y = dict(Y); Y.update({g: i for g in P}); tried[rule] += 1
                    if not efx0(v, [[g for g in goods if Y[g] == a] for a in agents]): bad += 1
        junk = [g for g in goods if all(vi.get(g, 0) == 0 for vi in v)]
        if junk:
            rel = [g for g in goods if g not in junk]
            for Y in all_efx0(agents, rel, v):
                own = {a: [g for g in rel if Y[g] == a] for a in agents}
                while True:                                             # envy-cycle elimination
                    G = nx.DiGraph([(a, b) for a in agents for b in agents
                                    if a != b and value(v[a], own[b]) > value(v[a], own[a])])
                    G.add_nodes_from(agents)
                    try: cyc = nx.find_cycle(G)
                    except nx.NetworkXNoCycle: break
                    own.update({a: own[b] for a, b in cyc}); rot += 1
                    if not efx0(v, [own[a] for a in agents]): junk_bad += 1
                src = next(a for a in agents if G.in_degree(a) == 0)
                own[src] = own[src] + junk; junk_tried += 1
                if not efx0(v, [own[a] for a in agents]): junk_bad += 1
    report("L2", bad == 0, f"n={n} m={m} values {vals}, every instance with |R_i| <= 3: {dict(tried)} "
           f"(peel, EFX0 allocation of the rest) pairs, {bad} not EFX0")
    report("L3", junk_bad == 0, f"same grid: {junk_tried} EFX0 allocations of the relevant goods, {rot} rotations, "
           f"junk to a source; {junk_bad} not EFX0  [{time.time() - t0:.0f}s]")

# ---------------------------------------------------------------------------------------------------- L8
def check_L8(ns=range(2, 9)):
    ok, msgs = True, []
    for n in ns:
        if n <= 7:
            cores = gen_cores_nauty(n, 2 * n)
            ok &= len(cores) == 1; msgs.append(f"n={n}: {len(cores)} core")
        # agent k: shared goods k-1, k (mod n) and private good n + k; the orientation gives agent k {k, n + k}
        sets = [((k - 1) % n, k, n + k) for k in range(n)]
        B = [[k, n + k] for k in range(n)]
        for k, S in enumerate(sets):                       # agent k's safety depends only on its own values
            for p in itertools.permutations(S):
                for t in BAL[::7]:
                    v = [{} for _ in range(n)]; v[k] = dict(zip(p, t))
                    ok &= safe(v, B, k)
    report("L8", ok, "genbg: exactly one connected core with m = 2n (" + ", ".join(msgs) + "); the orientation "
           f"allocation is safe for every agent under every ranking, n = {ns[0]}..{ns[-1]}")

# ---------------------------------------------------------------------------------------------------- L4, L7, L11
def kernel(H):
    """Suppress the degree-2 vertices of a connected graph with min degree >= 2 that is not a cycle: returns the
    branch vertices and the multigraph edges (u, w) (loops allowed), one per maximal path through degree-2 vertices."""
    branch = [u for u in H if H.degree(u) >= 3]
    paths = set()
    for u in branch:
        for w in H[u]:
            path, prev, cur = [u], u, w
            while H.degree(cur) == 2:
                path.append(cur); nxt = next(x for x in H[cur] if x != prev) if len(set(H[cur])) > 1 else prev
                prev, cur = cur, nxt
            path.append(cur)
            key = min(tuple(path), tuple(reversed(path)))
            paths.add(key)
    return branch, [(p[0], p[-1]) for p in paths]

def shape(branch, edges):
    if len(branch) == 1 and len(edges) == 2: return 'figure-eight'
    if len(branch) == 2 and len(edges) == 3:
        loops = sum(u == w for u, w in edges)
        return {0: 'theta', 2: 'dumbbell'}.get(loops, 'other')
    return 'other'

def check_L4_L11():
    t0 = time.time(); ok = True; tally = collections.Counter(); shapes = collections.Counter(); total = 0
    levels = [(n, m) for n in range(2, 7) for m in range(3, 2 * n + 1)] + [(7, m) for m in range(11, 15)]
    for n, m in levels:
        for pi, sets in gen_cores_nauty(n, m):
            total += 1
            deg = collections.Counter(g for S in sets for g in S)
            priv = sum(1 for g in deg if deg[g] == 1)
            ok &= set(deg) == set(range(m)) and priv == pi <= n and m <= 2 * n
            ok &= 3 * n == 2 * m - priv + sum(d - 2 for d in deg.values() if d >= 2)          # L4
            H = nx.Graph([(('a', i), ('g', g)) for i, S in enumerate(sets) for g in S])
            beta = H.number_of_edges() - H.number_of_nodes() + 1
            ok &= nx.is_connected(H) and beta == 2 * n - m + 1                                  # L7
            H.remove_nodes_from([('g', g) for g in deg if deg[g] == 1])                         # L11
            ok &= nx.is_connected(H) and min(d for _, d in H.degree()) >= 2
            ok &= H.number_of_edges() - H.number_of_nodes() + 1 == beta
            if beta == 1:
                ok &= all(d == 2 for _, d in H.degree()); tally['beta=1 cycle'] += 1; continue
            br, E = kernel(H)
            deg_k = collections.Counter(x for e in E for x in e)
            ok &= all(deg_k[u] == H.degree(u) >= 3 for u in br) and len(E) == len(br) + beta - 1
            ok &= len(br) <= 2 * beta - 2
            if beta == 2:
                s = shape(br, E); shapes[(n, s)] += 1; ok &= s != 'other'
    report("L4 L7 L11", ok, f"{total} connected cores (n = 2..6 all m; n = 7, m = 11..14): counting identity, "
           f"beta = 2n - m + 1, min degree >= 2 after deleting private goods, kernel min degree >= 3 with "
           f"V <= 2beta - 2 and E = V + beta - 1  [{time.time() - t0:.0f}s]")
    report("L11 beta=2", ok, "shapes: " + ", ".join(f"n={n} {s}: {c}" for (n, s), c in sorted(shapes.items())))

# ---------------------------------------------------------------------------------------------------- X2, L7, L9
X2 = [(1, 0, 6), (1, 0, 7), (2, 0, 8), (3, 0, 9), (2, 4, 5), (3, 4, 5)]      # agent: (a, b, c), a > b > c

def pair_partitions(goods):
    """Set partitions of `goods` into blocks of size 1 or 2."""
    if not goods: yield []; return
    g, rest = goods[0], goods[1:]
    for p in pair_partitions(rest): yield [[g]] + p
    for k, h in enumerate(rest):
        for p in pair_partitions(rest[:k] + rest[k + 1:]): yield [[g, h]] + p

def safe_in(vi, own, others):
    """Raw EFX0 for an agent with values vi holding `own` while the other bundles are `others`."""
    mine = value(vi, own)
    return all(value(vi, B) - vi.get(g, 0) <= mine for B in others for g in B)

def size2_brute(prof, reals, n=6, m=10):
    """Every allocation with all bundles <= 2: each partition of the goods into blocks of size <= 2 with at most n
    blocks, padded with empty bundles to n slots, and each of the n! assignments of slots to agents. An allocation is
    EFX0 iff every agent is safe, and an agent's safety depends only on its slot and the other slots, so the raw
    definition is evaluated once per (agent, slot) and looked up per assignment. Also checks L7 and L9."""
    vs = [[dict(zip(t, r)) for t in prof] for r in reals]
    count = good = l7bad = l9bad = 0
    perms = list(itertools.permutations(range(n)))
    for p in pair_partitions(list(range(m))):
        if len(p) > n: continue
        slots = p + [[] for _ in range(n - len(p))]
        e = n - len(p)
        l7bad += sum(len(S) == 1 for S in p) != 2 * n - m - 2 * e
        ok = [[None] * n for _ in range(n)]
        for i in range(n):
            for s, own in enumerate(slots):
                others = slots[:s] + slots[s + 1:]
                res = {safe_in(v[i], own, others) for v in vs}
                if len(res) != 1: raise SystemExit("realizations disagree")
                ok[i][s] = res.pop()
                l9 = all(value(vs[0][i], own) >= vs[0][i].get(g, 0) for B in others if len(B) == 2 for g in B)
                l9bad += l9 != ok[i][s]
        for sigma in perms:                                              # agent i gets slots[sigma[i]]
            count += 1
            good += all(ok[i][sigma[i]] for i in range(n))
    return count, good, l7bad, l9bad

def check_X2():
    t0 = time.time()
    reals = [(4, 3, 2), (10, 9, 2), (6, 5, 4)]                     # balanced: a < b + c
    alloc = [[0, 6], [1, 7, 8, 9], [2], [3], [4], [5]]
    ok = all(efx0([dict(zip(t, r)) for t in X2], alloc) for r in BAL)
    report("X2 allocation", ok, f"{alloc} is EFX0 under all {len(BAL)} balanced realizations (one bundle of 4)")
    count, good, l7bad, l9bad = size2_brute(X2, reals)
    report("X2 size<=2", count == 4082400 and good == 0 and l7bad == 0,
           f"{count} allocations with all bundles <= 2, EFX0: {good}; L7 alone-goods identity violated in {l7bad} "
           f"partitions  [{time.time() - t0:.0f}s]")
    report("L9", l9bad == 0, f"size-2 criterion vs raw definition for every agent and bundle of those allocations: "
           f"{l9bad} disagreements")
    alt = X2[:5] + [(3, 5, 4)]                                           # agent 5 ranks 5 above 4
    count2, good2, _, _ = size2_brute(alt, reals[:1])
    report("X2 control", good2 > 0, f"profile with agent 5 = (3, 5, 4): {good2} of {count2} size-<=2 allocations "
           f"are EFX0 (the brute force is not vacuous)  [{time.time() - t0:.0f}s]")

# ---------------------------------------------------------------------------------------------------- X3
def check_X3():
    v = [{0: 4, 1: 3, 2: 2} for _ in range(4)]                            # goods 3, 4, 5 worthless to everyone
    sols = [X for X in itertools.product(range(4), repeat=6) if efx0(v, bundles_of(X, 4))]
    small = [X for X in sols if max(collections.Counter(X).values()) <= 2]
    stated = efx0(v, [[0], [1], [2], [3, 4, 5]])
    report("X3", sols and not small and stated, f"4^6 allocations: {len(sols)} EFX0, {len(small)} of them with all "
           "bundles <= 2; {x}, {y}, {z}, {w1, w2, w3} is EFX0: " + str(stated))

# ---------------------------------------------------------------------------------------------------- D shape
def check_D_shape():
    import glob, gzip, json, os
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    msgs, ok = [], True
    for f in sorted(glob.glob(os.path.join(root, 'results', 'certs_*.json.gz'))):
        recs = json.load(gzip.open(f, 'rt')); big = collections.Counter()
        for r in recs:
            for X in r['allocations']:
                size = collections.Counter(X); big[sum(size[j] > 2 for j in range(r['n']))] += 1
        ok &= max(big) <= 1
        msgs.append(f"{os.path.basename(f)}: {len(recs)} hypergraphs, {sum(big.values())} allocations, "
                    f"by number of bundles with > 2 goods {dict(sorted(big.items()))}")
    report("D shape", ok, "; ".join(msgs))

if __name__ == '__main__':
    t0 = time.time()
    checks = {'L5': [check_L5], 'L2': [lambda: check_L2_L3(3, 4, (0, 1, 2)), lambda: check_L2_L3(2, 4, (0, 1, 2, 3))],
              'L8': [check_L8], 'L11': [check_L4_L11], 'X2': [check_X2], 'X3': [check_X3], 'D': [check_D_shape]}
    for name in sys.argv[1:] or list(checks):
        for f in checks[name]: f()
    print(f"step0_checks: {len(FAIL)} failures {FAIL}  [{time.time() - t0:.0f}s]")
    sys.exit(1 if FAIL else 0)
