"""Enumerate every connected k = 4 *multigraph core* with n agents (every good valued by at most two agents), one per
isomorphism class, with nauty's genbg, written for proof/k4-p3 (independent of k4/search4.py, which lists the k = 4 cores
used elsewhere). A multigraph core here satisfies the conditions of k4/check4.is_core: connected agent / good incidence
graph, every agent of degree 3 or 4, every good valued by somebody, at most d - 2 private goods for an agent of degree d;
and every good has degree at most 2. ((C4), p + q < s + t for an agent with two private goods p, q, is a condition on
values: the CEGAR's type domains impose it.) genbg -c -d3:1 -D4:2 n m lists the connected bipartite graphs with
agents of degree 3..4 and goods of degree 1..2 up to isomorphism (fixing the two classes), for m = 1..4n; the
private-good bound is then applied. Each core is re-checked with k4/check4.is_core.
Writes CHECKOUT/results/k4_certs_<n>_mg.json.gz in the format of results/k4_certs_*.json.gz ('cores': m, idx, sets),
so that k4/oc1cert/run.py of compute/k4-oc1max-cert can certify the list as '<n>_mg'.
    python3 k4/p3/mg_cores.py N CHECKOUT
"""
import sys, os, gzip, json, subprocess, shutil, collections
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.dirname(HERE))
import check4

GENBG = shutil.which('genbg') or shutil.which('nauty-genbg')


def cores(n):
    out = []
    for m in range(1, 4 * n + 1):
        r = subprocess.run([GENBG, '-cq', '-d3:1', '-D4:2', str(n), str(m)], capture_output=True)
        for line in r.stdout.split(b'\n'):
            if not line: continue
            G = nx.from_graph6_bytes(line)
            sets = [sorted(g - n for g in G[a]) for a in range(n)]
            deg = [G.degree(n + g) for g in range(m)]
            if any(sum(deg[g] == 1 for g in S) > len(S) - 2 for S in sets): continue
            assert check4.is_core(n, m, sets, False)[0] and max(deg) <= 2
            out.append({'m': m, 'idx': len(out), 'sets': sets})
    return out


if __name__ == '__main__':
    n, dst = int(sys.argv[1]), sys.argv[2]
    C = cores(n)
    print(f'n = {n}: {len(C)} connected multigraph cores;', 'by m:', dict(sorted(collections.Counter(c["m"] for c in C).items())),
          '; by number of 4-good agents:', dict(sorted(collections.Counter(sum(len(S) == 4 for S in c['sets']) for c in C).items())))
    with gzip.open(os.path.join(dst, 'results', f'k4_certs_{n}_mg.json.gz'), 'wt') as f:
        json.dump({'n': n, 'mode': 'multigraph cores (every good of degree <= 2), k4/p3/mg_cores.py', 'cores': C}, f)
