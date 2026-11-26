"""The frozen threat graph of a pre-allocation (k4/p3.md section 5). For the Phase 1 state (index insertion; upgrade
policy --pol, default 0 = none) of each instance:
  frozen agents F (pick base, pick in NA); for x in F, its *dumpable* goods D_x = goods of R_x ranked below its pick
  that are junk; its minimal threatening sets T subset of D_x with v_x(T) > v_x(pick).
  T-graph: vertices the junk goods, edges the threatening pairs; 'flat' = a frozen agent whose three dumpable goods
  pairwise threaten (a triangle of its own); 'triple-only' threats (a > b + c) are implied by any proper colouring.
Reports per instance: number of free agents, whether the T-graph is bipartite, its odd cycles' agents, flat agents,
and whether the state has a two-owner completion with no rotation (SAT, k4/p3/ts.extends with B = 2).
    python3 k4/p3/threat_graph.py SRC [--pol=0] [options of k4/p3/dump_rules.py]
"""
import sys, os, random, collections, json
import networkx as nx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *
import ts, dump_rules


def threat_graph(I, s):
    fr = s.frozen(); J = s.junk()
    G = nx.Graph(); G.add_nodes_from(J); flat = []; edges_by = collections.defaultdict(list)
    for x in range(I.n):
        if not fr[x]: continue
        (y,) = tuple(s.base[x]); vy = I.v[x][y]
        D = [g for g in I.sets[x] if g in J and (I.v[x][g], -g) < (vy, -y)]
        pairs = [(g, h) for i, g in enumerate(D) for h in D[i + 1:] if I.v[x][g] + I.v[x][h] > vy]
        if len(D) == 3 and len(pairs) == 3: flat.append(x)
        for g, h in pairs:
            G.add_edge(g, h); edges_by[(min(g, h), max(g, h))].append(x)
    return G, flat, edges_by


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1))); pol = int(opt.get('pol', 0))
    print('$ python3 k4/p3/threat_graph.py ' + ' '.join(sys.argv[1:]), flush=True)
    L = dump_rules.load(src, opt, rng)
    cnt = collections.Counter(); ex = []
    for I in L:
        s = ts.upgrade(ts.initial(I)[0], pol)
        G, flat, eb = threat_graph(I, s)
        bip = nx.is_bipartite(G)
        nfree = sum(not f for f in s.frozen())
        C = Complete(I); ok2 = ts.extends(I, C, s, 2, {2: C.big_bound(2)}) is not None
        key = f"free {'1' if nfree <= 1 else '>=2'}, T {'bipartite' if bip else 'odd cycle'}{', flat' if flat else ''}: two owners {'ok' if ok2 else 'FAIL'}"
        cnt[key] += 1
        if nfree >= 2 and bip and not flat and not ok2: ex.append((I.n, I.m, I.name, I.as_json(), [sorted(b) for b in s.base]))
        if not bip:
            cyc = [c for c in nx.cycle_basis(G) if len(c) % 2]
            print(f'  odd cycle in {I.name} (n={I.n}, m={I.m}): cycle {cyc[:1]}, agents {[eb[(min(a,b),max(a,b))] for a,b in zip(cyc[0], cyc[0][1:]+cyc[0][:1])] if cyc else "?"}', flush=True)
    for k, v in sorted(cnt.items()): print(f'  {k}: {v}')
    ex.sort()
    for e in ex[:3]:
        print('  free>=2, T bipartite, no flat, but no two-owner completion:', e[2], f'n={e[0]} m={e[1]}', 'bases', e[4])
        print('     ', json.dumps(e[3]))
