"""H_t (k4/c4.md section 7) and HH_t (k4/lemmam_bt.md section 3) built from their definitions, and Proposition HT of
k4/girth.md section 4: both hypergraphs are linear and, for t >= 2, the agent l (l_A) lies on no 3-cycle, so Theorem T1
(LSS with l as vertex 0) gives an EFX0 allocation for EVERY monotone valuation profile on them.

    python3 k4/girth/ht_families.py [TMAX] [PROFILES]
Checks the two structural facts for t <= TMAX, checks the instance against the suite copies (c4-H1, c4-H2, c4-H5,
lmbt-HH3), and runs LSS (vertex 0 = l, random labels of the others, random choices) on PROFILES random additive
profiles per t, raw EFX0 check.  The theorem needs no computation; this is a test of the statement and of the code.
"""
import random
import sys

from lss import Inst, lss, labels, random_labels, is_efx0, two_cycles, triangles


def H_sets(t, tag='', shared_u=None):
    """goods named by strings; returns (agents, sets) for H_t: agents l, x_{j,i}, y_j in index order"""
    agents, sets = [], []
    u = shared_u if shared_u is not None else 'u' + tag
    agents.append('l' + tag)
    sets.append(['g1' + tag, 'z' + tag, u, "u'" + tag])
    for j in range(1, t + 1):
        for i in range(1, 4):
            agents.append('x%d%d%s' % (j, i, tag))
            sets.append(['a%d%d%s' % (j, i, tag), 'b%d%d%s' % (j, i, tag), 'c%d%d%s' % (j, i, tag), 'g%d%s' % (j, tag)])
        agents.append('y%d%s' % (j, tag))
        e = ('g%d%s' % (j + 1, tag)) if j < t else 'z' + tag
        sets.append(['a%d1%s' % (j, tag), 'a%d2%s' % (j, tag), 'a%d3%s' % (j, tag), e])
    return agents, sets


H_VALUES = [8, 6, 5, 4], [8, 6, 4, 3], [8, 6, 4, 3]       # l; x; y (in the order of H_sets)


def build(t, double=False, values=None, rng=None):
    if not double:
        agents, sets = H_sets(t)
    else:
        a1, s1 = H_sets(t, 'A', 'u')
        a2, s2 = H_sets(t, 'B', 'u')
        agents = [a1[0], a2[0]] + a1[1:] + a2[1:]
        sets = [s1[0], s2[0]] + s1[1:] + s2[1:]
    names = sorted({g for S in sets for g in S})
    idx = {g: k for k, g in enumerate(names)}
    isets = [[idx[g] for g in S] for S in sets]
    if rng is not None:
        vals = [[rng.randint(1, 30) for _ in S] for S in isets]
    else:
        vals = []
        for a, S in zip(agents, isets):
            v = H_VALUES[0] if a[0] == 'l' else H_VALUES[1]
            vals.append(list(v))
    return agents, Inst(isets, vals, len(names))


def on_triangle(I):
    on = set()
    for x, y, z, w in triangles(I):
        on |= {x, y, z}
    return on


def incidence(I):
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from((('a', i), {'k': 'a'}) for i in range(I.n))
    G.add_nodes_from((('g', g), {'k': 'g'}) for g in range(I.m))
    G.add_edges_from((('a', i), ('g', g), {'v': I.v[i][g]}) for i in range(I.n) for g in I.R[i])
    return G


def same_as_suite():
    import networkx as nx
    from networkx.algorithms.isomorphism import GraphMatcher
    from sources import suite
    S = dict(suite())
    for name, t, double in (('c4-H1', 1, False), ('c4-H2', 2, False), ('c4-H5', 5, False), ('lmbt-HH3', 3, True)):
        _, I = build(t, double)
        gm = GraphMatcher(incidence(I), incidence(S[name]), node_match=lambda a, b: a['k'] == b['k'],
                          edge_match=lambda a, b: a['v'] == b['v'])
        print('%s: the built instance (with its values) is isomorphic to the suite copy: %s' % (name, gm.is_isomorphic()))
        assert gm.is_isomorphic()


def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    prof = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    rng = random.Random(1)
    print('$ python3 k4/girth/ht_families.py', tmax, prof)
    same_as_suite()
    for double in (False, True):
        for t in range(1, tmax + 1):
            agents, I = build(t, double)
            free = sorted(agents[a] for a in range(I.n) if a not in on_triangle(I))
            ok = 0
            for p in range(prof):
                _, J = build(t, double, rng=rng)
                r = lss(J, lab=random_labels(J, 0, rng), pick=rng if p % 2 else 'max')
                if t >= 2:                                 # Theorem T1's hypothesis holds: no break at all
                    assert r.first_break is None and r.soft_break is None and r.props[2], (t, double)
                ok += is_efx0(J, r.X)
            print('%s_%d: n=%d m=%d linear=%s, agents on no 3-cycle: %s; LSS with vertex 0 = %s EFX0 on %d/%d random '
                  'profiles' % ('HH' if double else 'H', t, I.n, I.m, not two_cycles(I), free or 'none', agents[0],
                                ok, prof))
            if t >= 2:
                assert not two_cycles(I) and agents[0] in free and ok == prof


if __name__ == '__main__':
    main()
