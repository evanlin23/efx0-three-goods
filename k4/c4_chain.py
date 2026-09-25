"""The gadget chain H_t of k4/c4.md §7: LB4r with index insertion needs at least ceil(2t/3) nested rotations.

H_t (t >= 1) has goods g_1..g_t, z, u, u', and a_ji, b_ji, c_ji (j = 1..t, i = 1..3); m = 10t + 3. Agents, in index
order: l = {g_1, z, u, u'} with values (8, 6, 5, 4); then for each j: x_j1, x_j2, x_j3 with x_ji = {a_ji, b_ji, c_ji, g_j}
and values (8, 6, 4, 3), and y_j = {a_j1, a_j2, a_j3, e_j} with values (8, 6, 4, 3), where e_j = g_{j+1} (j < t) and
e_t = z. n = 4t + 1.

Usage:
  python3 k4/c4_chain.py check T1,T2,...      core conditions, strict types, and the explicit allocation of §7 checked
                                               against the raw EFX0 definition (independent of lb4.c)
  python3 k4/c4_chain.py run T1,... OPTS ...  run k4/c4_lb4w.c (64-bit lb4.c) with each option string on H_t
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

if __name__ == '__main__':
    mode, ts = sys.argv[1], [int(x) for x in sys.argv[2].split(',')]
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
