"""The gadget chain H_t of k4/c4.md §7: LB4r with index insertion needs at least ceil(2t/3) nested rotations.

H_t (t >= 1) has goods g_1..g_t, z, u, u', and a_ji, b_ji, c_ji (j = 1..t, i = 1..3); m = 10t + 3. Agents, in index
order: l = {g_1, z, u, u'} with values (8, 6, 5, 4); then for each j: x_j1, x_j2, x_j3 with x_ji = {a_ji, b_ji, c_ji, g_j}
and values (8, 6, 4, 3), and y_j = {a_j1, a_j2, a_j3, e_j} with values (8, 6, 4, 3), where e_j = g_{j+1} (j < t) and
e_t = z. n = 4t + 1.

Usage:
  python3 k4/c4_chain.py check T1,T2,...      core conditions, strict types, and the explicit allocation of §7 checked
                                               against the raw EFX0 definition (independent of lb4.c)
  python3 k4/c4_chain.py run T1,... OPTS ...  run k4/c4_lb4w.c (64-bit lb4.c) with each option string on H_t
  python3 k4/c4_chain.py reach T Q            the structural steps of Proposition H's proof on every valid state reachable
                                               from Phase 1 (index insertion) with at most Q rotations, with the
                                               independent tracer k4/c4tools/c4trace.py (Phase 1, validity, need chains,
                                               rotations): the Phase 1 state, no upgrade under either policy, every need
                                               an a of the agent's own gadget, every chain inside one gadget, and the
                                               per-gadget count (slots minus forced goods: -2 untouched, <= +1 touched,
                                               <= 0 for l; a rotated one-good base gets a slot); prints the largest total
"""
import itertools, os, subprocess, sys, tempfile, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))

def build(t):
    nxt = [0]
    def new():
        g = nxt[0]; nxt[0] += 1; return g
    g = [new() for _ in range(t)]; z = new(); u = new(); u2 = new()
    sets = [[g[0], z, u, u2]]; vals = [[8, 6, 5, 4]]
    names = {g[0]: 'g1', z: 'z', u: 'u', u2: "u'"}
    for j in range(t):
        a = [new() for _ in range(3)]; b = [new() for _ in range(3)]; c = [new() for _ in range(3)]
        for i in range(3):
            sets.append([a[i], b[i], c[i], g[j]]); vals.append([8, 6, 4, 3])
        sets.append([a[0], a[1], a[2], g[j + 1] if j + 1 < t else z]); vals.append([8, 6, 4, 3])
    return sets, vals, nxt[0]

def explicit_allocation(t):
    """y_j gets a_j1, x_j1 gets {b_j1, c_j1}, x_j2 and x_j3 get {a, b}, l (the owner) gets everything else."""
    sets, vals, m = build(t)
    n = len(sets); own = [0] * m      # default: l (agent 0)
    for j in range(t):
        base = 1 + 4 * j
        x = [sets[base + i] for i in range(3)]
        own[x[0][0]] = base + 3                      # a_j1 -> y_j
        own[x[0][1]] = base; own[x[0][2]] = base     # b_j1, c_j1 -> x_j1
        for i in (1, 2):
            own[x[i][0]] = base + i; own[x[i][1]] = base + i   # a_ji, b_ji -> x_ji
    return [[g for g in range(m) if own[g] == i] for i in range(n)]

def efx0(sets, vals, X):
    v = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    for i in range(len(sets)):
        mine = sum(v[i].get(g, 0) for g in X[i])
        for j in range(len(sets)):
            if j != i and X[j] and mine < sum(v[i].get(g, 0) for g in X[j]) - min(v[i].get(g, 0) for g in X[j]):
                return False
    return True

def core_ok(sets, vals, m):
    """k = 4 core conditions (k4/SCOUT.md §2) and strict types; connectivity."""
    deg = [sum(g in s for s in sets) for g in range(m)]
    if min(deg) == 0: return 'unvalued good'
    for S, V in zip(sets, vals):
        if len(S) not in (3, 4): return 'size'
        if 2 * max(V) >= sum(V): return 'not strictly balanced'
        priv = [k for k, g in enumerate(S) if deg[g] == 1]
        if len(priv) > len(S) - 2: return 'too many private goods'
        if len(priv) == 2 and sum(V[k] for k in priv) >= sum(V) - sum(V[k] for k in priv): return 'p + q >= s + t'
        for r1 in range(1, len(S) + 1):          # strict: disjoint nonempty subsets have different values
            for A in itertools.combinations(range(len(S)), r1):
                rest = [k for k in range(len(S)) if k not in A]
                for r2 in range(1, len(rest) + 1):
                    for B in itertools.combinations(rest, r2):
                        if sum(V[k] for k in A) == sum(V[k] for k in B): return 'tie'
    seen = {0}; st = [0]
    while st:
        a = st.pop()
        for b in range(len(sets)):
            if b not in seen and set(sets[a]) & set(sets[b]): seen.add(b); st.append(b)
    return 'ok' if len(seen) == len(sets) else 'disconnected'

def encode(sets, vals, m):
    out = [f"{len(sets)} {m}"]
    for S, V in zip(sets, vals):
        out.append(f"{len(S)} {' '.join(map(str, S))} 1"); out.append(' '.join(map(str, V)))
    return '\n'.join(out) + '\n'

def binary():
    src = os.path.join(HERE, 'c4_lb4w.c')
    b = os.path.join(tempfile.gettempdir(), 'k4_c4_lb4w_' + hashlib.sha256(open(src, 'rb').read()).hexdigest()[:16])
    if not os.path.exists(b): subprocess.run(['gcc', '-O2', '-o', b, src], check=True, stderr=subprocess.DEVNULL)
    return b

def reach(t, Q):
    sys.path.insert(0, os.path.join(HERE, 'c4tools'))
    import c4trace as T
    sets, vals, m = build(t)
    I = T.Inst(sets, vals); n = I.n
    gad = [None] + [(i - 1) // 4 for i in range(1, n)]                       # gadget of each agent (None for l)
    A = [frozenset(sets[1 + 4 * j + 3][:3]) for j in range(t)]              # a's of gadget j
    g1 = sets[0][0]; u, u2 = sets[0][2], sets[0][3]
    st0 = T.initial_state(I, [])[0]
    # Phase 1 as in the proof
    ok = st0.Y[0] == g1
    for j in range(t):
        for i in range(3):
            x = 1 + 4 * j + i; ok &= st0.Y[x] == sets[x][0]
        ok &= st0.Y[1 + 4 * j + 3] == sets[1 + 4 * j + 3][3]
    Jexp = {u, u2} | {g for j in range(t) for i in range(3) for g in sets[1 + 4 * j + i][1:3]}
    ok &= set(st0.J) == Jexp
    fr0 = st0.frozen()
    ok &= all(fr0[i] == (i > 0 and (i - 1) % 4 != 3) for i in range(n))
    ok &= all(T.upgrades(st0, mode).base == st0.base for mode in (1, 2))
    print(f'  Phase 1 (picks, junk, frozen = the x\'s, no upgrade under policies 1 and 2) as in the proof: {ok}, '
          f'omega = {st0.omega()}', flush=True)
    base0 = list(st0.base)
    key = lambda s: (tuple(s.base), tuple(s.kind))
    seen = {key(st0): 0}; level = [st0]; bad = []; worst = {}
    def audit(s, d):
        if s.base[0] != frozenset([g1]) or s.kind[0] != 'pick' or s.needs(0): bad.append(('l', d)); return
        for i in range(1, n):
            if not s.needs(i) <= A[gad[i]]: bad.append(('needs', i, d)); return
        fr = s.frozen()
        for k in range(n):
            if fr[k]:
                for ch in T.chains_from(s, k):
                    if len({gad[x] for x in ch}) != 1: bad.append(('chain', ch, d)); return
        cap = s.caps(rot_slot=True)
        tot = cap[0] - (1 if {u, u2} <= s.J else 0)
        if tot > 0: bad.append(('l count', d)); return
        touched = 0
        for j in range(t):
            ag = range(1 + 4 * j, 5 + 4 * j)
            forced = sum(1 for x in ag if (x - 1) % 4 != 3 and s.kind[x] == 'pick' and s.base[x] == frozenset([sets[x][0]])
                         and set(sets[x][1:3]) <= s.J)
            c = sum(cap[x] for x in ag) - forced
            if any(s.base[x] != base0[x] or s.kind[x] != 'pick' for x in ag):
                touched += 1
                if c > 1: bad.append(('touched count', j, c, d)); return
            elif c != -2: bad.append(('untouched count', j, c, d)); return
            tot += c
        if touched > d: bad.append(('touched', touched, d)); return
        worst[d] = max(worst.get(d, -99), tot)
    audit(st0, 0)
    for d in range(1, Q + 1):
        nxt = []
        for s in level:
            fr = s.frozen()
            for k in range(n):
                if not fr[k]: continue
                for ch in T.chains_from(s, k):
                    for O in T.rot_options(s, ch):
                        ns = T.rotate(s, ch, O)
                        if not ns.valid() or key(ns) in seen: continue
                        seen[key(ns)] = d; nxt.append(ns); audit(ns, d)
        level = nxt
        print(f'  {d} rotation(s): {len(nxt)} new valid states; largest total (slots minus forced goods) '
              f'{worst.get(d)}; proof bound (t - s) - 2s with s = max(t - {d}, 0): {t - 3 * max(t - d, 0)}', flush=True)
    print(f'  every structural step of the proof holds on all {len(seen)} states: {not bad}' + (f' {bad[:3]}' if bad else ''))

if __name__ == '__main__':
    mode, ts = sys.argv[1], [int(x) for x in sys.argv[2].split(',')]
    if mode == 'reach':
        for t in ts:
            print(f'H_{t}: reachable states with at most {sys.argv[3]} rotations', flush=True); reach(t, int(sys.argv[3]))
        sys.exit(0)
    for t in ts:
        sets, vals, m = build(t)
        print(f'H_{t}: n = {len(sets)}, m = {m}', flush=True)
        if mode == 'check':
            X = explicit_allocation(t)
            big = sum(len(B) > 2 for B in X)
            print(f'  core conditions: {core_ok(sets, vals, m)}; explicit allocation EFX0: {efx0(sets, vals, X)}, '
                  f'bundles with more than 2 goods: {big} (the owner l: {len(X[0])} goods)', flush=True)
        else:
            for opt in sys.argv[3:]:
                p = subprocess.run([binary()] + opt.split() + ['-f1'], input=encode(sets, vals, m),
                                   capture_output=True, text=True)
                o = p.stdout.split()
                print(f'  lb4 {opt}: ' + ' '.join(o[6:18]) + f'  largest bundle {o[-1]}', flush=True)
                for line in p.stderr.strip().split('\n'):
                    if line: print('    ' + line[:160] + (' ...' if len(line) > 160 else ''), flush=True)
