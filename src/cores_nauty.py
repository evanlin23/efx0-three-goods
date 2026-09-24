"""Connected-core enumeration with nauty's genbg, written independently of frontier.gen_cores (PROMPT.md Step 0).
A connected core with n agents and m goods is a connected bipartite graph (agents on one side, goods on the other) in
which every agent has degree 3, every good has degree >= 1, and no agent has two goods of degree 1 (at most one private
good). genbg (C) lists the connected bicoloured graphs with these degree bounds, one per isomorphism class (isomorphisms
map agents to agents and goods to goods); we keep those with at most one private good per agent.
Output matches gen_cores: a list of (pi, sets), agents holding a private good first, private goods numbered last.
Usage: cores_nauty.py n:m [n:m ...]                counts and timings
       cores_nauty.py --cross-check n:m [n:m ...]  compare with frontier.gen_cores up to isomorphism (bijection)"""
import shutil, subprocess, sys, time
import networkx as nx

GENBG = shutil.which('genbg') or shutil.which('nauty-genbg')

def gen_cores_nauty(n, m):
    if GENBG is None:
        raise SystemExit("nauty's genbg not found: apt-get install nauty (or brew install nauty), "
                         "or run frontier.py with --enum python")
    args = [GENBG, '-cq', '-d3:1', f'-D3:{n}', str(n), str(m), f'{3 * n}:{3 * n}']
    out = []
    for line in subprocess.run(args, capture_output=True, text=True, check=True).stdout.split():
        G = nx.from_graph6_bytes(line.encode())
        nbrs = [sorted(g - n for g in G[i]) for i in range(n)]
        assert all(len(S) == 3 for S in nbrs) and all(G.degree(n + g) >= 1 for g in range(m))
        deg = [G.degree(n + g) for g in range(m)]
        priv = [[g for g in S if deg[g] == 1] for S in nbrs]
        if any(len(p) > 1 for p in priv): continue
        order = sorted(range(n), key=lambda i: not priv[i])            # agents with a private good first
        shared = [g for g in range(m) if deg[g] >= 2]
        pi = sum(1 for p in priv if p)
        label = {g: k for k, g in enumerate(shared)}
        label.update({priv[i][0]: len(shared) + k for k, i in enumerate(order[:pi])})
        sets = [sorted(label[g] for g in nbrs[i] if deg[g] >= 2) + [label[g] for g in priv[i]] for i in order]
        out.append((pi, sets))
    return out

def incidence(n, sets):
    G = nx.Graph()
    for i, S in enumerate(sets):
        G.add_node(('a', i), kind='agent')
        for g in S: G.add_node(('g', g), kind='good'); G.add_edge(('a', i), ('g', g))
    return G

def cross_check(n, m):
    """Pair every core of gen_cores(n, m) with an isomorphic core from gen_cores_nauty(n, m); True iff a bijection."""
    from frontier import gen_cores
    A = [incidence(n, s) for _, s in gen_cores(n, m)]
    B = [incidence(n, s) for _, s in gen_cores_nauty(n, m)]
    same = lambda x, y: x['kind'] == y['kind']
    buckets = {}
    for k, G in enumerate(B): buckets.setdefault(nx.weisfeiler_lehman_graph_hash(G, node_attr='kind'), []).append(k)
    used = set()
    for G in A:
        cand = [k for k in buckets.get(nx.weisfeiler_lehman_graph_hash(G, node_attr='kind'), [])
                if k not in used and nx.is_isomorphic(G, B[k], node_match=same)]
        if not cand: return False, len(A), len(B)
        used.add(cand[0])
    return len(used) == len(A) == len(B), len(A), len(B)

if __name__ == '__main__':
    check = '--cross-check' in sys.argv
    for arg in (a for a in sys.argv[1:] if a != '--cross-check'):
        n, m = map(int, arg.split(':')); t0 = time.time()
        if check:
            ok, a, b = cross_check(n, m)
            print(f"n={n} m={m}: gen_cores {a}, genbg {b}, isomorphism bijection: {'YES' if ok else 'NO'}"
                  f"  [{time.time() - t0:.0f}s]", flush=True)
            if not ok: sys.exit(1)
        else:
            print(f"n={n} m={m}: {len(gen_cores_nauty(n, m))} connected cores  [{time.time() - t0:.1f}s]", flush=True)
