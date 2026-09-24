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
  local_search.py py n [m ...] [--jobs=N]                        Python two-phase check (independent, slow: n <= 4)
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


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    opts = dict(a[2:].split('=', 1) for a in sys.argv[1:] if a.startswith('--') and '=' in a)
    jobs = int(opts.get('jobs', os.cpu_count() or 1))
    if args and args[0] == 'reach687':
        profs = [int(x) for x in open(args[1]).read().split()]
        reach("6 9 1 6 7 4 5 8 0 1 5 0 3 6 2 3 5 2 4 6", profs, opts.get('moves', 'ESRAUCX')); sys.exit(0)
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
