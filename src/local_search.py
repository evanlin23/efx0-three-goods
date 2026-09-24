"""Local search for EFX0 in cores (workstream proof/local-search; proofs/local_search.md).

Two things live here:
  1. A driver for the C checkers ls_check.c (every partial EFX0 state of a core has an improving move?) and
     ls_twophase.c (every stable junk-free partial allocation can be completed by placing the unallocated goods as
     junk in source bundles?). It enumerates connected cores with cores_nauty.py, compiles the C code with gcc,
     splits the cores over --jobs processes and prints the checkers' output.
  2. An independent Python implementation of the two-phase check (--py), written from the definitions in
     proofs/local_search.md, sharing no code with ls_twophase.c: EFX0 and envy are decided from the RAW definition with
     two numeric balanced realizations of every ranking (they must agree, since EFX0 in a core is ordinal), the
     enumeration is profile-outer and state-inner, and the junk placement is searched by brute force over all
     assignments of the unallocated goods to the agents. It must report the same numbers of stable states and of
     failures as the C checker (ls_twophase -x).

Usage:
  local_search.py twophase n [m ...] [--jobs=N] [--flags=-x]    C two-phase check (ls_twophase)
  local_search.py allstates n [m ...] [--jobs=N] [--flags=-O]   C all-states local search check (ls_check)
  local_search.py alg n [m ...] [--jobs=N] [--cert=FILE.json.gz] Algorithm LS2 (Theorem C) on every profile; certificate
  local_search.py py n [m ...] [--jobs=N]                        Python two-phase check (independent, slow: n <= 4)
  local_search.py pyalg n [m ...]                                Algorithm LS2 in Python (numeric) on every profile
  local_search.py pyrandom N_LO N_HI TRIALS [--seed=S]           Algorithm LS2 in Python on random cores and values
  local_search.py stuck6                                         replay the n = 6 stuck run of the one-phase search
  local_search.py lemma1                                         Lemma 1 (partial safety rule) vs the raw definition
  local_search.py twophase687                                    the n = 6 counterexample to TP with moves M1, M2 only
  local_search.py reach687 FILE [--moves=ESRAUCX]                reachability of core 687's stuck states (profiles in FILE)
"""
import itertools, os, subprocess, sys, multiprocessing, time

HERE = os.path.dirname(os.path.abspath(__file__))
PERMS = list(itertools.permutations(range(3)))
REAL = [(4.0, 3.0, 2.0), (10.0, 9.0, 2.0)]        # two balanced realizations of a > b > c


def cores(n, ms):
    sys.path.insert(0, HERE)
    from cores_nauty import gen_cores_nauty
    out = []
    for m in ms:
        out += [(n, m, sets) for _, sets in gen_cores_nauty(n, m)]
    return out


def compile_c(name):
    """compile src/<name>.c into a temporary directory (keeps binaries out of the repository)"""
    import tempfile
    build = os.path.join(tempfile.gettempdir(), 'efx0_local_search')
    os.makedirs(build, exist_ok=True)
    exe = os.path.join(build, name)
    src = os.path.join(HERE, name + '.c')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-o', exe, src], check=True)
    return exe


def run_c(name, flags, core_list, jobs):
    exe = compile_c(name)
    lines = [f"{n} {m} " + ' '.join(str(g) for S in sets for g in S) for n, m, sets in core_list]
    chunks = [lines[k::jobs] for k in range(jobs)]
    procs = [subprocess.Popen([exe] + flags, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
             for c in chunks if c]
    for p, c in zip(procs, chunks):
        p.stdin.write('\n'.join(c) + '\n'); p.stdin.close()
    rc = 0
    for p in procs:
        out = p.stdout.read(); p.wait(); rc |= p.returncode
        sys.stdout.write(out)
    return rc


# ---------------------------------------------------------------- independent Python implementation (raw definition)
def val(prof_R, i, goods, r):
    """value of a set of goods for agent i under realization r; prof_R[i] = (a, b, c)"""
    a, b, c = prof_R[i]
    w = {a: REAL[r][0], b: REAL[r][1], c: REAL[r][2]}
    return sum(w.get(g, 0.0) for g in goods)


def raw_efx0(R, bundles, r):
    n = len(R)
    for i in range(n):
        own = val(R, i, bundles[i], r)
        for j in range(n):
            if j == i or len(bundles[j]) < 2: continue
            vs = [val(R, i, [g], r) for g in bundles[j]]
            if sum(vs) - min(vs) > own + 1e-9: return False
    return True


def decide(f):
    """evaluate f(r) under both realizations; they must agree (ordinality)"""
    x, y = f(0), f(1)
    if x != y: raise SystemExit("realizations disagree: ordinality violated")
    return x


def to_bundles(n, owner):
    B = [[] for _ in range(n)]
    for g, o in enumerate(owner):
        if o is not None: B[o].append(g)
    return B


def stable_and_placeable(n, m, sets, R, owner, use_s7=True):
    """owner: junk-free partial allocation (tuple, None = unallocated). Returns (stable, placeable)."""
    B = to_bundles(n, owner)
    U = [g for g in range(m) if owner[g] is None]
    Rset = [set(t) for t in R]
    if not decide(lambda r: raw_efx0(R, B, r)): return None
    # (s2) nobody envies an unallocated good
    if decide(lambda r: any(val(R, i, [u], r) > val(R, i, B[i], r) for i in range(n) for u in U if u in Rset[i])):
        return (False, None)
    # (s3) envy graph acyclic
    env = [[decide(lambda r: i != j and val(R, i, B[j], r) > val(R, i, B[i], r)) for j in range(n)] for i in range(n)]
    color = [0] * n
    def cyc(v):
        color[v] = 1
        for w in range(n):
            if env[v][w] and (color[w] == 1 or (color[w] == 0 and cyc(w))): return True
        color[v] = 2; return False
    if any(color[v] == 0 and cyc(v) for v in range(n)): return (False, None)
    def efx_after(newB):
        return decide(lambda r: raw_efx0(R, newB, r))
    def better(i, Z, r):
        return val(R, i, Z, r) > val(R, i, B[i], r)
    # (s5) single-agent valued rebundle
    for i in range(n):
        avail = sorted((set(B[i]) | set(U)) & Rset[i])
        for k in range(1, len(avail) + 1):
            for Z in itertools.combinations(avail, k):
                if not decide(lambda r: better(i, Z, r)): continue
                newB = [list(x) for x in B]; newB[i] = list(Z)
                if efx_after(newB): return (False, None)
    # (s6) champion path s = t0 -> ... -> tr = k (r >= 1): t_q takes its own goods of B[t_{q+1}], k takes Z within
    #      R_k and B[s] + U, the rest of B[s] becomes unallocated
    def paths(v, seen):
        yield [v]
        for w in range(n):
            if env[v][w] and w not in seen:
                for p in paths(w, seen | {w}): yield [v] + p
    for s in range(n):
        for p in paths(s, {s}):
            if len(p) < 2: continue
            k = p[-1]
            avail = sorted((set(B[s]) | set(U)) & Rset[k])
            for kk in range(1, len(avail) + 1):
                for Z in itertools.combinations(avail, kk):
                    if not decide(lambda r: better(k, Z, r)): continue
                    newB = [list(x) for x in B]
                    for q in range(len(p) - 1):
                        newB[p[q]] = [g for g in B[p[q + 1]] if g in Rset[p[q]]]
                    newB[k] = list(Z)
                    if efx_after(newB): return (False, None)
    # (s7) augmented envy cycle i_0 -> ... -> i_{L-1} -> i_0 (L >= 2): Z_t within R_{i_t} and B[i_{t+1}] + U, meeting
    #      B[i_{t+1}], disjoint, each strictly better; all other goods of the cycle's bundles become unallocated
    for L in (range(2, n + 1) if use_s7 else []):
        for cycle in itertools.permutations(range(n), L):
            if cycle[0] != min(cycle): continue
            def assign(t, used, Zs):
                if t == L:
                    newB = [list(x) for x in B]
                    for q in range(L): newB[cycle[q]] = list(Zs[q])
                    return efx_after(newB)
                i, nx = cycle[t], cycle[(t + 1) % L]
                avail = sorted(((set(B[nx]) | set(U)) & Rset[i]) - used)
                for kk in range(1, len(avail) + 1):
                    for Z in itertools.combinations(avail, kk):
                        if not set(Z) & set(B[nx]): continue
                        if not decide(lambda r: better(i, Z, r)): continue
                        if assign(t + 1, used | set(Z), Zs + [Z]): return True
                return False
            if assign(0, set(), []): return (False, None)
    # stable: brute-force junk placement of U over all agents (junk only: u to an agent that does not value it)
    for choice in itertools.product(range(n), repeat=len(U)):
        if any(U[k] in Rset[j] for k, j in enumerate(choice)): continue
        newB = [list(x) for x in B]
        for k, j in enumerate(choice): newB[j].append(U[k])
        if efx_after(newB): return (True, True)
    return (True, False)


def py_core(task):
    n, m, sets = task
    valuers = [[i for i in range(n) if g in sets[i]] for g in range(m)]
    stable = fail = 0; examples = []
    for prof in itertools.product(range(6), repeat=n):
        R = [tuple(sets[i][p] for p in PERMS[prof[i]]) for i in range(n)]
        for owner in itertools.product(*[[None] + v for v in valuers]):
            if None not in owner: continue
            res = stable_and_placeable(n, m, sets, R, owner)
            if res is None or not res[0]: continue
            stable += 1
            if not res[1]:
                fail += 1
                if len(examples) < 3: examples.append((R, to_bundles(n, owner)))
    return n, m, sets, stable, fail, examples



# ------------------------------------------------ one-phase local search: moves on arbitrary partial allocations (Python)
def potential(R, B, r=0):
    """(sum of levels, allocated goods); levels are compared through values, so use the level index of the chain"""
    chain = lambda i, S: sorted(val(R, i, list(T), r) for k in range(4) for T in itertools.combinations(R[i], k)).index(
        val(R, i, [g for g in S if g in R[i]], r))
    return (sum(chain(i, B[i]) for i in range(len(R))), sum(len(x) for x in B))


def successors(R, m, B):
    """all partial allocations reachable by one move E, S, R, A, U, C or X (proofs/local_search.md, section 2) that
    are EFX0 (raw definition) and raise the potential"""
    n = len(R); Rset = [set(t) for t in R]
    P = [g for g in range(m) if not any(g in x for x in B)]
    held = {g: j for j in range(n) for g in B[j]}
    junk = {g for g, j in held.items() if g not in Rset[j]}
    env = [[i != j and decide(lambda r: val(R, i, B[j], r) > val(R, i, B[i], r)) for j in range(n)] for i in range(n)]
    p0 = decide(lambda r: potential(R, B, r))
    out = []
    def emit(kind, newB):
        newB = [sorted(x) for x in newB]
        if decide(lambda r: raw_efx0(R, newB, r)) and decide(lambda r: potential(R, newB, r)) > p0:
            out.append((kind, newB))
    for g in P:                                                      # E and A
        for j in range(n):
            newB = [list(x) for x in B]; newB[j].append(g); emit('E' if not B[j] else 'A', newB)
    for i in range(n):                                               # S and U: i's new bundle within X_i + P + junk
        avail = sorted(set(B[i]) | set(P) | (junk - set(B[i])))
        for k in range(len(avail) + 1):
            for Y in itertools.combinations(avail, k):
                if sorted(Y) == sorted(B[i]): continue
                newB = [[g for g in x if g not in Y] for x in B]; newB[i] = list(Y); emit('U', newB)
    def cycles():
        for L in range(2, n + 1):
            for cyc in itertools.permutations(range(n), L):
                if cyc[0] == min(cyc): yield cyc
    for cyc in cycles():                                             # R: envy-cycle rotation
        if all(env[cyc[q]][cyc[(q + 1) % len(cyc)]] for q in range(len(cyc))):
            newB = [list(x) for x in B]
            for q in range(len(cyc)): newB[cyc[q]] = list(B[cyc[(q + 1) % len(cyc)]])
            emit('R', newB)
    def paths(v, seen):
        yield [v]
        for w in range(n):
            if env[v][w] and w not in seen:
                for p in paths(w, seen | {w}): yield [v] + p
    for s in range(n):                                               # C: champion along an envy path
        for p in paths(s, {s}):
            if len(p) < 2: continue
            k = p[-1]; avail = sorted(set(B[s]) | set(P))
            for kk in range(1, len(avail) + 1):
                for Z in itertools.combinations(avail, kk):
                    newB = [list(x) for x in B]
                    for q in range(len(p) - 1): newB[p[q]] = list(B[p[q + 1]])
                    newB[k] = list(Z); emit('C', newB)
    for cyc in cycles():                                             # X: augmented envy cycle (own goods, junk allowed)
        L = len(cyc)
        def assign(t, used, Zs):
            if t == L:
                newB = [list(x) for x in B]
                for q in range(L): newB[cyc[q]] = []
                taken = set().union(*[set(z) for z in Zs])
                newB = [[g for g in x if g not in taken] for x in newB]
                for q in range(L): newB[cyc[q]] = list(Zs[q])
                emit('X', newB); return
            i, nx = cyc[t], cyc[(t + 1) % L]
            avail = sorted(((set(B[nx]) | set(P) | (junk - set(B[i]))) & Rset[i]) - used)
            for kk in range(1, len(avail) + 1):
                for Z in itertools.combinations(avail, kk):
                    if set(Z) & set(B[nx]) and decide(lambda r: val(R, i, Z, r) > val(R, i, B[i], r)):
                        assign(t + 1, used | set(Z), Zs + [Z])
        assign(0, set(), [])
    return out


# the n = 6 stuck state (attempts/local-search-one-phase-n6.md): core 687 of genbg's list for n = 6, m = 9
STUCK6_R = [(1, 6, 7), (4, 5, 8), (1, 5, 0), (6, 0, 3), (5, 2, 3), (4, 6, 2)]       # rankings (a, b, c)
STUCK6_SEQ = [('E', 1, 0), ('E', 4, 1), ('E', 0, 2), ('E', 6, 3), ('E', 5, 4), ('E', 2, 5), ('A', 8, 2), ('A', 7, 5)]


def verify_stuck6():
    R, m, n = STUCK6_R, 9, 6
    B = [[] for _ in range(n)]
    print("rankings (a,b,c):", R)
    for kind, g, j in STUCK6_SEQ:
        cand = [nb for k, nb in successors(R, m, B)]
        newB = [sorted(x) for x in B]; newB[j] = sorted(newB[j] + [g])
        assert newB in cand, (kind, g, j)
        B = newB
        print(f"  move {kind}: good {g} to agent {j} -> {B}, potential {decide(lambda r: potential(R, B, r))}")
    succ = successors(R, m, B)
    print("final state", B, "unallocated", [g for g in range(m) if not any(g in x for x in B)],
          "EFX0:", decide(lambda r: raw_efx0(R, B, r)), "- improving moves (E,S,R,A,U,C,X):", len(succ))
    return 0 if not succ else 1


def lemma1_check():
    """Lemma 1 against the raw definition: agent 0 values goods 0, 1, 2 (each ranking), goods 3, 4, 5 are worthless to
    it; every good is unallocated or with one of four agents; three balanced realizations."""
    reals = [(2.0, 1.5, 1.0), (10.0, 9.0, 2.0), (5.0, 3.0, 2.5)]
    n, m = 4, 6; checked = mism = 0
    for p in itertools.permutations(range(3)):
        a, b, c = p
        for owner in itertools.product(range(-1, n), repeat=m):
            size = [sum(1 for o in owner if o == j) for j in range(n)]
            free = lambda g: owner[g] < 0 or size[owner[g]] == 1
            S = {g for g in (a, b, c) if owner[g] == 0}
            if len(S) >= 2: rule = True
            elif S == {a}: rule = not (owner[b] >= 0 and owner[b] == owner[c] and size[owner[b]] >= 3)
            elif S == {b}: rule = free(a)
            elif S == {c}: rule = free(a) and free(b)
            else: rule = free(a) and free(b) and free(c)
            B = [[g for g in range(m) if owner[g] == j] for j in range(n)]
            for r in reals:
                w = dict(zip(p, r)); own = sum(w.get(g, 0.0) for g in B[0])
                raw = all(len(B[j]) < 2 or sum(w.get(g, 0.0) for g in B[j]) - min(w.get(g, 0.0) for g in B[j]) <= own + 1e-9
                          for j in range(1, n))
                checked += 1; mism += raw != rule
    print(f"Lemma 1 vs raw definition: {checked} checks, {mism} mismatches")
    return 1 if mism else 0


def reach(core_line, profiles, moves):
    """reachability (ls_check -r -p) of stuck states from the empty allocation, one profile at a time"""
    exe = compile_c('ls_check'); total = 0
    for p in profiles:
        out = subprocess.run([exe, '-r', '-m', moves, '-p', str(p), '-l', '0'], input=core_line + '\n',
                             capture_output=True, text=True).stdout
        line = [l for l in out.splitlines() if l.startswith('TOTAL')][0]
        k = int(line.split('stuck ')[1].split(';')[0]); total += k
        print(f"profile {p}: {line}", flush=True)
    print(f"REACH TOTAL: {len(profiles)} profiles, stuck states reachable from the empty allocation: {total}")


def verify_twophase687():
    """the counterexample to TP with Phase 1 moves M1, M2 only (attempts/local-search-twophase-m1m2.md)"""
    sets = [[1, 6, 7], [4, 5, 8], [0, 1, 5], [0, 3, 6], [2, 3, 5], [2, 4, 6]]
    R = [(1, 6, 7), (4, 5, 8), (0, 1, 5), (0, 3, 6), (2, 3, 5), (2, 4, 6)]
    Y = [[1], [4], [5], [0], [2], [6]]
    owner = tuple(next((j for j in range(6) if g in Y[j]), None) for g in range(9))
    print("rankings (a,b,c):", R, "\nY:", Y, "unallocated:", [g for g in range(9) if owner[g] is None])
    r12 = stable_and_placeable(6, 9, sets, R, owner, use_s7=False)
    print("stable under M1, M2 (and s2, s3):", r12[0], "- some junk placement over all agents is EFX0:", r12[1])
    r123 = stable_and_placeable(6, 9, sets, R, owner, use_s7=True)
    print("stable under M1, M2, M3:", r123[0])
    newB = [[6, 7], [5, 8], [1], [0], [2], [4]]
    ok = decide(lambda r: raw_efx0(R, newB, r))
    fin = [[6, 7], [5, 8], [1, 3], [0], [2], [4]]
    print("augmented cycle 0->5->1->2->0 gives", newB, "EFX0:", ok,
          "; then good 3 with agent 2:", fin, "EFX0:", decide(lambda r: raw_efx0(R, fin, r)))
    return 0 if (r12 == (True, False) and not r123[0] and ok) else 1


def run_alg(core_list, jobs, cert_path=None):
    """run ls_alg (Algorithm LS2) on every profile of every core; optionally write a certificate for check_certs.py"""
    import gzip, json
    exe = compile_c('ls_alg')
    lines = [f"{n} {m} " + ' '.join(str(g) for S in sets for g in S) for n, m, sets in core_list]
    chunks = [lines[k::jobs] for k in range(jobs)]
    flags = ['-c'] if cert_path else []
    procs = [subprocess.Popen([exe] + flags, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
             for c in chunks if c]
    for p, c in zip(procs, chunks):
        p.stdin.write('\n'.join(c) + '\n'); p.stdin.close()
    import threading
    outs = [[] for _ in procs]
    def drain(k):                      # read every process concurrently (a full pipe would stall a checker)
        outs[k] = procs[k].stdout.readlines()
    threads = [threading.Thread(target=drain, args=(k,)) for k in range(len(procs))]
    for t in threads: t.start()
    for t in threads: t.join()
    recs, rc = [], 0
    for p, lines_k in zip(procs, outs):
        p.wait(); rc |= p.returncode
        for line in lines_k:
            if line.startswith('CERT '): recs.append(json.loads(line[5:]))
            else: sys.stdout.write(line)
    if cert_path:
        with gzip.open(cert_path, 'wt') as f: json.dump(recs, f)
        print(f"wrote {cert_path}: {len(recs)} cores, {sum(len(r['allocations']) for r in recs)} allocations")
    return rc


# ------------------------------------------ Algorithm LS2 in Python, from numeric valuations (independent of ls_alg.c)
class LS2Failure(Exception):
    pass


def ls2_numeric(vals, m):
    """vals[i] = {good: value > 0} with exactly three goods, balanced. Returns a complete allocation (owner list).
    Every decision uses the numeric values; every step is checked (EFX0 by the raw definition, Pareto improvement)."""
    n = len(vals)
    V = lambda i, S: sum(vals[i].get(g, 0.0) for g in S)
    top = [max(vals[i], key=vals[i].get) for i in range(n)]
    bottom = [set(vals[i]) - {top[i]} for i in range(n)]
    Y = [set() for _ in range(n)]
    def U(): return set(range(m)) - set().union(*Y)
    def raw_ok():
        for i in range(n):
            for j in range(n):
                if i != j and len(Y[j]) >= 2 and V(i, Y[j]) - min(vals[i].get(g, 0.0) for g in Y[j]) > V(i, Y[i]) + 1e-9:
                    return False
        return True
    def envy(i, j): return i != j and V(i, Y[j]) > V(i, Y[i]) + 1e-12
    def graph():
        E = [[envy(i, j) for j in range(n)] for i in range(n)]
        indeg = [sum(E[i][j] for i in range(n)) for j in range(n)]
        R = [row[:] for row in E]
        for k in range(n):
            for i in range(n):
                if R[i][k]:
                    for j in range(n):
                        if R[k][j]: R[i][j] = True
        return E, indeg, R
    def path(E, s, t):
        prev = {s: None}; q = [s]
        for v in q:
            for w in range(n):
                if E[v][w] and w not in prev: prev[w] = v; q.append(w)
        if t not in prev: return None
        p = [t]
        while prev[p[-1]] is not None: p.append(prev[p[-1]])
        return p[::-1]
    def takes(pairs):   # pairs: list of (agent, new bundle); every other good of these agents' bundles goes to U
        taken = set().union(*[Z for _, Z in pairs])
        assert all(len(Z1 & Z2) == 0 for k, (_, Z1) in enumerate(pairs) for _, Z2 in pairs[k + 1:])
        for a, _ in pairs: Y[a] = set()
        for j in range(n): Y[j] -= taken
        for a, Z in pairs: Y[a] = set(Z)
    def is_a_holder(i): return Y[i] == {top[i]}
    def step():
        E, indeg, R = graph(); u_set = U()
        for i in range(n):                                                                   # 1
            for u in u_set:
                if vals[i].get(u, 0.0) > V(i, Y[i]) + 1e-12: takes([(i, {u})]); return 1
        for s in range(n):                                                                   # 2
            if R[s][s]:
                cyc, v, seen = [], s, set()
                while v not in seen:
                    seen.add(v); cyc.append(v)
                    v = next(w for w in range(n) if E[v][w] and (w == s or R[w][s]))
                cyc = cyc[cyc.index(v):]
                takes([(a, Y[cyc[(k + 1) % len(cyc)]] & set(vals[a])) for k, a in enumerate(cyc)]); return 2
        for i in range(n):                                                                   # 3, 4
            if is_a_holder(i):
                inU = bottom[i] & u_set
                if len(inU) == 2: takes([(i, set(bottom[i]))]); return 3
                if inU and not any(E[k][i] for k in range(n)): takes([(i, Y[i] | inU)]); return 4
        one = [s for s in range(n) if indeg[s] == 0 and len(Y[s]) == 1]
        for s in one:                                                                        # 5
            w = set(vals[s]) & u_set
            if w: takes([(s, Y[s] | {min(w)})]); return 5
        if any(not Y[j] for j in range(n)): return 0
        trip = [(i, u, s) for s in one for i in range(n) if is_a_holder(i)
                for u in u_set if bottom[i] == {u} | Y[s]]
        for i, u, s in trip:                                                                 # 6
            if R[s][i]:
                p = path(E, s, i)
                takes([(p[k], Y[p[k + 1]] & set(vals[p[k]])) for k in range(len(p) - 1)] + [(i, {u} | Y[s])]); return 6
        # 7: system of distinct representatives of the dirty sets (bipartite matching)
        D = {s: [t for t in trip if t[2] == s] for s in one}
        match = {}
        def aug(s, seen):
            for t in D[s]:
                u = t[1]
                if u in seen: continue
                seen.add(u)
                if u not in match or aug(match[u][2], seen): match[u] = t; return True
            return False
        if not all(aug(s, set()) for s in one): return 0
        rep = {t[2]: t for t in match.values()}
        f = {}
        for s in one:
            i = rep[s][0]
            s2 = [s1 for s1 in one if s1 != s and R[s1][i]]
            if not s2: raise LS2Failure("dirty a-holder not reachable from another one-good source")
            f[s] = s2[0]
        v, seen = one[0], set()
        while v not in seen: seen.add(v); v = f[v]
        fc = [v]
        while f[fc[-1]] != v: fc.append(f[fc[-1]])
        walk = []                     # list of (agent, next agent, kind, triple)
        cur = fc[0]
        for _ in fc:
            sj = next(x for x in fc if f[x] == cur)
            i, u, _s = rep[sj]
            p = path(E, cur, i)
            walk += [(p[k], p[k + 1], 'envy', None) for k in range(len(p) - 1)] + [(i, sj, 'dirty', rep[sj])]
            cur = sj
        verts = [e[0] for e in walk] + [cur]
        pos = {}
        for k, x in enumerate(verts):
            if x in pos: seg = walk[pos[x]:k]; break
            pos[x] = k
        pairs = [(a, (Y[b] & set(vals[a])) if kind == 'envy' else ({t[1]} | Y[b])) for a, b, kind, t in seg]
        if not any(kind == 'dirty' for _, _, kind, _ in seg): raise LS2Failure("cycle without dirty edge")
        takes(pairs); return 7
    steps = 0
    while U():
        before = [V(i, Y[i]) for i in range(n)]
        k = step()
        if not k: break
        steps += 1
        after = [V(i, Y[i]) for i in range(n)]
        if not raw_ok(): raise LS2Failure(f"step {k} broke EFX0")
        if any(a < b - 1e-9 for a, b in zip(after, before)) or not any(a > b + 1e-9 for a, b in zip(after, before)):
            raise LS2Failure(f"step {k} is not a Pareto improvement")
        if any(g not in vals[i] for i in range(n) for g in Y[i]): raise LS2Failure("junk in Phase 1")
    u_set = U()
    if u_set:                                                                                # Phase 2
        E, indeg, R = graph()
        empty = [j for j in range(n) if not Y[j]]
        if empty: Y[empty[0]] |= u_set
        else:
            one = [s for s in range(n) if indeg[s] == 0 and len(Y[s]) == 1]
            trip = [(i, u, s) for s in one for i in range(n) if is_a_holder(i) for u in u_set if bottom[i] == {u} | Y[s]]
            match = {}
            def aug2(s, seen):
                for i, u, s_ in trip:
                    if s_ != s or u in seen: continue
                    seen.add(u)
                    if u not in match or aug2(match[u], seen): match[u] = s; return True
                return False
            unmatched = [s for s in one if not aug2(s, set())]
            if not unmatched: raise LS2Failure("Phase 2 with a saturating matching")
            star = unmatched[0]; T, q, DT = {star}, [star], set()
            for s in q:
                for i, u, s_ in trip:
                    if s_ == s:
                        DT.add(u)
                        if u not in match: raise LS2Failure("Hall: unmatched dirty good")
                        if match[u] not in T: T.add(match[u]); q.append(match[u])
            for u in u_set: Y[match[u] if u in DT else star].add(u)
    owner = [None] * m
    for j in range(n):
        for g in Y[j]: owner[g] = j
    if None in owner: raise LS2Failure("incomplete")
    if not raw_ok(): raise LS2Failure("final allocation not EFX0")
    return owner, steps


def random_core(n, rng):
    """a random core with n agents (not necessarily connected): 3 goods each, every good used, <= 1 private good
    per agent; m is drawn so that the counting identity of L4 can hold (n + 1 <= m <= 2n)"""
    while True:
        m = rng.randint(max(3, n // 2 + 2), 2 * n)
        sets = [rng.sample(range(m), 3) for _ in range(n)]
        deg = [0] * m
        for S in sets:
            for g in S: deg[g] += 1
        if min(deg) == 0 or any(sum(deg[g] == 1 for g in S) > 1 for S in sets): continue
        return m, sets


def random_balanced(rng):
    while True:
        a, b, c = sorted((rng.uniform(1, 10) for _ in range(3)), reverse=True)
        if a < b + c and a > b > c: return a, b, c


def pyalg_random(n_lo, n_hi, trials, seed):
    import random
    rng = random.Random(seed); runs = 0; steps_max = 0
    for n in range(n_lo, n_hi + 1):
        for _ in range(trials):
            m, sets = random_core(n, rng)
            vals = []
            for S in sets:
                a, b, c = random_balanced(rng); order = rng.sample(S, 3)
                vals.append({order[0]: a, order[1]: b, order[2]: c})
            try:
                _, st = ls2_numeric(vals, m)
            except LS2Failure as e:
                print("FAILURE", e, "n", n, "m", m, "vals", vals); return 1
            runs += 1; steps_max = max(steps_max, st)
        print(f"n={n}: {trials} random cores with random balanced values: all complete EFX0 (raw), max Phase-1 steps "
              f"{steps_max}", flush=True)
    print(f"PYALG RANDOM: {runs} runs, 0 failures (seed {seed})")
    return 0


def pyalg_exhaustive(core_list):
    """every profile of every listed core, realization (4, 3, 2) per ranking"""
    runs = 0
    for n, m, sets in core_list:
        for prof in itertools.product(range(6), repeat=n):
            vals = [dict(zip([sets[i][p] for p in PERMS[prof[i]]], (4.0, 3.0, 2.0))) for i in range(n)]
            try:
                ls2_numeric(vals, m)
            except LS2Failure as e:
                print("FAILURE", e, sets, prof); return 1
            runs += 1
    print(f"PYALG EXHAUSTIVE: {len(core_list)} cores, {runs} (core, profile) runs, 0 failures")
    return 0


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opts = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    jobs = int(opts.get('jobs', os.cpu_count() or 1))
    if args and args[0] == 'reach687':
        profs = [int(x) for x in open(args[1]).read().split()]
        reach("6 9 1 6 7 4 5 8 0 1 5 0 3 6 2 3 5 2 4 6", profs, opts.get('moves', 'ESRAUCX')); sys.exit(0)
    if args and args[0] == 'pyrandom':
        lo, hi, trials = int(args[1]), int(args[2]), int(args[3])
        sys.exit(pyalg_random(lo, hi, trials, int(opts.get('seed', 1))))
    if args and args[0] == 'twophase687':
        sys.exit(verify_twophase687())
    if args and args[0] == 'lemma1':
        sys.exit(lemma1_check())
    if args and args[0] == 'stuck6':
        sys.exit(verify_stuck6())
    mode, n = args[0], int(args[1])
    ms = [int(x) for x in args[2:]] or list(range(3, 2 * n + 1))
    core_list = cores(n, ms)
    t0 = time.time()
    if mode == 'twophase':
        flags = opts.get('flags', '-x').split()
        rc = run_c('ls_twophase', flags, core_list, jobs)
    elif mode == 'allstates':
        flags = opts.get('flags', '-O').split()
        rc = run_c('ls_check', flags, core_list, jobs)
    elif mode == 'alg':
        rc = run_alg(core_list, jobs, opts.get('cert'))
    elif mode == 'pyalg':
        rc = pyalg_exhaustive(core_list)
    elif mode == 'py':
        tot_s = tot_f = 0
        with multiprocessing.Pool(jobs) as pool:
            for n_, m_, sets, s, f, ex in pool.imap(py_core, core_list):
                tot_s += s; tot_f += f
                print(f"core n={n_} m={m_} goods {sets}: stable {s}, fail {f}", flush=True)
                for e in ex: print("   FAIL", e)
        print(f"PY TOTAL cores {len(core_list)}, stable junk-free states {tot_s}, junk placement fails {tot_f}")
        rc = 1 if tot_f else 0
    else:
        raise SystemExit(__doc__)
    print(f"[{mode} n={n} m={ms}: {len(core_list)} cores, {time.time() - t0:.0f}s]")
    sys.exit(rc)


if __name__ == '__main__':
    main()
