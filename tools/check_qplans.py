"""Independent checker for the Q-plan file of Lemma 7 (proofs/beta3.md), written without src/beta3.py or networkx.
For every record (a connected core with m = 2n - 2):
  1. checks it is a connected core (3 distinct goods per agent, every good used, <= 1 private good per agent);
  2. decides from scratch whether it is reduced: every component of H minus its branch vertices (H = incidence graph
     without private goods, branch = degree >= 3) contains at most one agent, or at most two if both of its end edges
     go to the same good; the file's 'reduced' flag must agree;
  3. for a reduced core, checks that there is a Q-plan for each of the 6^q rankings of its Q-agents (agents without a
     private good), in itertools.product order, and that each satisfies the definition of section 3:
       Y_z is {a}, {b}, {a,b}, {a,c} or {b,c}; the Y_z and the spares Z are disjoint sets of shared goods;
       Y_z = {b} only if a_z is the single good of another Q-agent with |Y| = 1;
       (P1) every component C of K (shared goods, P-agents as edges) has eps(C) = |E(C)| - |V(C)| + #(Y u Z in C) >= 0;
       (P2) a component with eps >= 1 contains no good of a 2-holder and no spare;
       (P3) if Z is nonempty and no component has eps >= 1: a dump target T, which is Y_z of a 2-holder or {v} for a
            shared good v outside Y u Z; otherwise T is absent. L = Z u T;
       (P4) Y_z = {a}: not both b_z, c_z in L;  (P5) Y_z = {b}: a_z not in L.
Usage: check_qplans.py qplans.json.gz [--expect n:reduced_count ...]
Completeness of the core list itself: run tools/check_enum.py on the same file."""
import sys, json, gzip, itertools, collections

PERMS = list(itertools.permutations(range(3)))


def find(par, x):
    while par[x] != x:
        par[x] = par[par[x]]; x = par[x]
    return x


def core_ok(n, m, sets):
    if len(sets) != n or m != 2 * n - 2 or any(len(set(S)) != 3 for S in sets): return False
    deg = collections.Counter(g for S in sets for g in S)
    if set(deg) != set(range(m)) or any(sum(deg[g] == 1 for g in S) > 1 for S in sets): return False
    par = list(range(n + m))
    for i, S in enumerate(sets):
        for g in S: par[find(par, i)] = find(par, n + g)
    return len({find(par, v) for v in range(n + m)}) == 1


def reduced(n, m, sets):
    deg = collections.Counter(g for S in sets for g in S)
    adj = collections.defaultdict(list)                     # H as adjacency lists, vertices ('a', i) and ('g', g)
    for i, S in enumerate(sets):
        for g in S:
            if deg[g] >= 2: adj[('a', i)].append(('g', g)); adj[('g', g)].append(('a', i))
    branch = {v for v in adj if len(adj[v]) >= 3}
    seen = set()
    for v in adj:
        if v in branch or v in seen: continue
        comp, stack, ends = [], [v], []                     # a component of H - branch: a path
        seen.add(v)
        while stack:
            x = stack.pop(); comp.append(x)
            for y in adj[x]:
                if y in branch: ends.append(y)
                elif y not in seen: seen.add(y); stack.append(y)
        agents = sum(1 for x in comp if x[0] == 'a')
        limit = 2 if len(ends) == 2 and ends[0] == ends[1] and ends[0][0] == 'g' else 1
        if agents > limit: return False
    return True


def check_plan(n, m, sets, Q, qrank, plan):
    deg = collections.Counter(g for S in sets for g in S)
    shared = {g for g in range(m) if deg[g] >= 2}
    Yl, Z, T = plan
    Y = {z: tuple(gs) for z, gs in zip(Q, Yl)}
    held = [g for gs in Y.values() for g in gs]
    if len(set(held)) != len(held) or len(set(Z)) != len(Z) or set(held) & set(Z): return "not disjoint"
    if not set(held) | set(Z) <= shared: return "not shared goods"
    single = {Y[z][0] for z in Q if len(Y[z]) == 1}
    for z in Q:
        a, b, c = qrank[z]
        if Y[z] not in [(a,), (b,), (a, b), (a, c), (b, c)]: return "not a role"
        if Y[z] == (b,) and not any(Y[w] == (a,) or (len(Y[w]) == 1 and Y[w][0] == a) for w in Q if w != z):
            return "b-pin without a single-good holder of a_z"
    par = {g: g for g in shared}                            # components of K
    Pedges = []
    for i, S in enumerate(sets):
        if any(deg[g] == 1 for g in S):
            x, y = [g for g in S if deg[g] >= 2]; Pedges.append((x, y)); par[find(par, x)] = find(par, y)
    comp = {g: find(par, g) for g in shared}
    eps = collections.Counter()
    for g in shared: eps[comp[g]] -= 1
    for x, y in Pedges: eps[comp[x]] += 1
    for g in held + list(Z): eps[comp[g]] += 1
    two_or_spare = {comp[g] for z in Q if len(Y[z]) == 2 for g in Y[z]} | {comp[g] for g in Z}
    for C, e in eps.items():
        if e < 0: return "(P1)"
        if e >= 1 and C in two_or_spare: return "(P2)"
    active = any(e >= 1 for e in eps.values())
    if Z and not active:
        if T is None: return "(P3) no dump target"
        T = tuple(T)
        if not (any(len(Y[z]) == 2 and Y[z] == T for z in Q)
                or (len(T) == 1 and T[0] in shared and T[0] not in held and T[0] not in Z)): return "(P3) bad target"
        L = set(Z) | set(T)
    else:
        if T is not None: return "(P3) target without need"
        L = set(Z)
    for z in Q:
        a, b, c = qrank[z]
        if Y[z] == (a,) and b in L and c in L: return "(P4)"
        if Y[z] == (b,) and a in L: return "(P5)"
    return None


if __name__ == '__main__':
    args = sys.argv[1:]
    recs = json.load(gzip.open(args[0], 'rt'))
    expect = {int(e.split(':')[0]): int(e.split(':')[1]) for e in args[2:]} if '--expect' in args else {}
    problems, count, red, nplans = 0, collections.Counter(), collections.Counter(), 0
    for r in recs:
        n, m, sets = r['n'], r['m'], [list(S) for S in r['sets']]
        count[n] += 1
        if not core_ok(n, m, sets): print("not a connected beta = 3 core:", sets); problems += 1; continue
        red_here = reduced(n, m, sets)
        if red_here != r['reduced']: print("reduced flag wrong:", sets); problems += 1
        if not red_here: continue
        red[n] += 1
        deg = collections.Counter(g for S in sets for g in S)
        Q = [i for i, S in enumerate(sets) if all(deg[g] >= 2 for g in S)]
        if r.get('Q') != Q: print("Q-agents wrong:", sets); problems += 1; continue
        plans = r.get('plans', [])
        if len(plans) != 6 ** len(Q): print("missing plans:", sets); problems += 1; continue
        for qp, plan in zip(itertools.product(range(6), repeat=len(Q)), plans):
            qrank = {z: tuple(sets[z][k] for k in PERMS[p]) for z, p in zip(Q, qp)}
            err = check_plan(n, m, sets, Q, qrank, plan)
            nplans += 1
            if err: print(f"bad plan ({err}):", sets, qp, plan); problems += 1
    for n, c in expect.items():
        if red[n] != c: print(f"expected {c} reduced cores with n = {n}, found {red[n]}"); problems += 1
    print(f"checked {len(recs)} cores {dict(sorted(count.items()))}; reduced {dict(sorted(red.items()))}; "
          f"{nplans} Q-plans; problems: {problems}")
    sys.exit(1 if problems else 0)
