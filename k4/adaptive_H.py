"""LB4r with an adaptive insertion rule (k4/adaptive.c) on the cores H_t of k4/c4.md §7 and on relabeled copies.

H_t (built as in k4/c4_chain.py of proof/k4-c4, whose build() is copied here unchanged): goods g_1..g_t, z, u, u' and
a_ji, b_ji, c_ji; agents l = {g_1, z, u, u'} (8, 6, 5, 4); for each gadget j, x_j1..x_j3 = {a_ji, b_ji, c_ji, g_j}
(8, 6, 4, 3) and y_j = {a_j1, a_j2, a_j3, e_j} (8, 6, 4, 3), e_j = g_{j+1}, e_t = z. n = 4t + 1, m = 10t + 3.
A relabeling permutes the agents and the goods (seeded); an adaptive rule's choices depend on indices only through
its tie-breaks, and #33 shows every fixed insertion order fails on some relabeled H_5.
Usage: adaptive_H.py T1,T2,... [--perms=K] [--seed=S] [--timeout=SEC] [C options, e.g. -A2 -r3 -w0]"""
import os, random, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adaptive_run as A

def build(t):
    nxt = [0]
    def new():
        g = nxt[0]; nxt[0] += 1; return g
    g = [new() for _ in range(t)]; z = new(); u = new(); u2 = new()
    sets = [[g[0], z, u, u2]]; vals = [[8, 6, 5, 4]]
    for j in range(t):
        a = [new() for _ in range(3)]; b = [new() for _ in range(3)]; c = [new() for _ in range(3)]
        for i in range(3):
            sets.append([a[i], b[i], c[i], g[j]]); vals.append([8, 6, 4, 3])
        sets.append([a[0], a[1], a[2], g[j + 1] if j + 1 < t else z]); vals.append([8, 6, 4, 3])
    return sets, vals, nxt[0]

def relabel(sets, vals, m, rng):
    n = len(sets); pa = list(range(n)); rng.shuffle(pa); pg = list(range(m)); rng.shuffle(pg)
    S = [None] * n; V = [None] * n
    for i in range(n):
        items = sorted(zip((pg[g] for g in sets[i]), vals[i]))      # goods of each agent listed in increasing index
        S[pa[i]] = [g for g, _ in items]; V[pa[i]] = [v for _, v in items]
    return S, V, pa

def main():
    args = sys.argv[1:]
    ts = [int(x) for x in args[0].split(',')]
    perms = int(next((a.split('=')[1] for a in args if a.startswith('--perms=')), 0))
    seed = int(next((a.split('=')[1] for a in args if a.startswith('--seed=')), 1))
    tmo = int(next((a.split('=')[1] for a in args if a.startswith('--timeout=')), 3600))
    opts = [a for a in args[1:] if a.startswith('-') and not a.startswith('--')]
    A.build()
    print('#', 'adaptive_H.py', ' '.join(args), flush=True)
    for t in ts:
        sets, vals, m = build(t)
        rng = random.Random(seed * 1000 + t)
        for p in range(perms + 1):
            S, V, pa = (sets, vals, None) if p == 0 else relabel(sets, vals, m, rng)
            t0 = time.time()
            try:
                r = subprocess.run([A.BIN] + opts + (['-T1'] if not any(o.startswith('-T') for o in opts) else []),
                                   input=A.encode_profile(S, V), capture_output=True, text=True, timeout=tmo)
                out = r.stdout.strip().split('\n')
                res = [l for l in out if l.startswith('single')]
                runs = [l for l in out if l.startswith('RUN')]
                tag = res[0] if res else f'exit {r.returncode}'
            except subprocess.TimeoutExpired:
                tag, runs = f'timeout {tmo}s', []
            lab = 'H_%d' % t + ('' if p == 0 else f' relabel {p} (l -> agent {pa[0]})')
            print(f"{lab}: {tag} time {time.time() - t0:.1f}s", flush=True)
            for l in runs: print('  ', l[:400], flush=True)

if __name__ == '__main__':
    main()
