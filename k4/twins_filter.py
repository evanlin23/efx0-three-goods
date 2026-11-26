"""Structural filter for minimal-counterexample candidate lists (k4/TWINS.md, row K4.MC8): a candidate core that
contains a certified double edge cannot be a minimal counterexample to TARGET4 (or one within C_beta).

A double edge is a pair of agents e, f sharing two goods that no other agent values. The kinds are read off the core
(P3: 3 goods, one private; Q3: 3 goods, none; P4: 4 goods, one private; Q4: 4 goods, none), the closure c is the
number of further goods e and f have in common (any degree). Certified for every profile (k4/TWINS.md §3):
  Q3-Q3 (c = 0, 1), Q3-P4 (c = 0, 1), Q3-Q4 (c = 1), P4-P4 (c = 0, 1), P4-Q4 (c = 1).
A pair whose kinds are P3 + anything is K4.MC3 / K4.MC5 territory and is not handled here.

Domain cuts (partially reduced double edges): the profiles of a configuration that no reduction covers are written by
k4/check_twins4.py --uncovered-out (one JSON file per certificate; types as {good: value} on the configuration's
labels). If a core contains the configuration, then under EVERY identification (labeling) of the configuration's goods
with the core's goods the pair's profile must be one of them; cut_domains() cuts each agent's type domain to the
intersection, over the labelings, of the projections. Types are matched by their ordinal signature (signs of
v(A) - v(B) over disjoint nonempty A, B), so any representatives may be used on either side.

Usage as a module: excluded(sets) -> None or a string naming the double edge;
  cut_domains(sets, dom, uncovered) -> (dom', rules) with dom[i] a list of value vectors aligned with sets[i];
as a script:
  twins_filter.py CANDIDATES.json.gz [UNCOVERED.json ...]   (records with 'sets', as written by mincex_shapes.py /
                                                             mc_n.py; with uncovered files, also the domain cuts)
"""
import sys, gzip, json, collections, itertools

ORDER = ('Q3', 'P4', 'Q4')
CERTIFIED = {('Q3', 'Q3', 0), ('Q3', 'Q3', 1), ('Q3', 'P4', 0), ('Q3', 'P4', 1), ('Q3', 'Q4', 1),
             ('P4', 'P4', 0), ('P4', 'P4', 1), ('P4', 'Q4', 1)}


def kinds(sets):
    deg = collections.Counter(g for S in sets for g in S)
    out = []
    for S in sets:
        p = sum(deg[g] == 1 for g in S)
        out.append({(3, 1): 'P3', (3, 0): 'Q3', (4, 1): 'P4', (4, 0): 'Q4'}.get((len(S), p), 'other'))
    return out, deg


def double_edges(sets):
    """(i, j, kind_i, kind_j, c) for every pair sharing >= 2 goods of degree 2 (kinds ordered Q3 < P4 < Q4)."""
    kd, deg = kinds(sets)
    out = []
    for i, j in itertools.combinations(range(len(sets)), 2):
        sh = set(sets[i]) & set(sets[j])
        if sum(deg[g] == 2 for g in sh) < 2: continue
        a, b = (i, j) if (kd[i] not in ORDER or kd[j] not in ORDER or ORDER.index(kd[i]) <= ORDER.index(kd[j])) else (j, i)
        out.append((a, b, kd[a], kd[b], len(sh) - 2))
    return out


def excluded(sets):
    for i, j, ki, kj, c in double_edges(sets):
        if (ki, kj, c) in CERTIFIED: return 'dbl-%s-%s%s (agents %d, %d)' % (ki, kj, '-c%d' % c if c else '', i, j)
    return None


def gamma_prune(nb):
    """The same exclusion at the level of G' (agent neighbourhoods of shared goods, as in mincex_shapes.gammas), before
    each agent of degree 3 is made Q3 or P4: two agents of G'-degree 3 sharing two goods of degree 2 (any closure), or
    one of degree 3 and one of degree 4 sharing two goods of degree 2 and a third good. Equivalent to excluded() on
    every core with that G' (whatever the Q3/P4 choice), since Q3-Q3, Q3-P4 and P4-P4 are certified for c = 0, 1 and
    Q3-Q4, P4-Q4 for c = 1."""
    deg = collections.Counter(g for N in nb for g in N)
    for i, j in itertools.combinations(range(len(nb)), 2):
        di, dj = sorted((len(nb[i]), len(nb[j])))
        sh = set(nb[i]) & set(nb[j])
        if sum(deg[g] == 2 for g in sh) < 2: continue
        if (di, dj) == (3, 3) or ((di, dj) == (3, 4) and len(sh) >= 3): return True
    return False


# configuration labels, in the order of k4/check_twins4.py's hard-coded configurations
LABELS = {
    ('Q3', 'Q3', 0): (['g0', 'g1', 'a'], ['g0', 'g1', 'x']), ('Q3', 'Q3', 1): (['g0', 'g1', 'a'], ['g0', 'g1', 'a']),
    ('Q3', 'P4', 0): (['g0', 'g1', 'a'], ['g0', 'g1', 'x', 'pf']), ('Q3', 'P4', 1): (['g0', 'g1', 'a'], ['g0', 'g1', 'a', 'pf']),
    ('Q3', 'Q4', 0): (['g0', 'g1', 'a'], ['g0', 'g1', 'x', 'y']), ('Q3', 'Q4', 1): (['g0', 'g1', 'a'], ['g0', 'g1', 'a', 'y']),
    ('P4', 'P4', 0): (['g0', 'g1', 'a', 'pe'], ['g0', 'g1', 'x', 'pf']), ('P4', 'P4', 1): (['g0', 'g1', 'a', 'pe'], ['g0', 'g1', 'a', 'pf']),
    ('P4', 'Q4', 0): (['g0', 'g1', 'a', 'pe'], ['g0', 'g1', 'x', 'y']), ('P4', 'Q4', 1): (['g0', 'g1', 'a', 'pe'], ['g0', 'g1', 'a', 'y']),
    ('Q4', 'Q4', 0): (['g0', 'g1', 'a', 'b'], ['g0', 'g1', 'x', 'y']), ('Q4', 'Q4', 1): (['g0', 'g1', 'a', 'b'], ['g0', 'g1', 'a', 'y']),
    ('Q4', 'Q4', 2): (['g0', 'g1', 'a', 'b'], ['g0', 'g1', 'a', 'b']),
}


def config_name(ki, kj, c):
    return 'dbl-%s-%s%s' % (ki, kj, '-c%d' % c if c else '')


def signature(vals):
    n = len(vals)
    out = []
    for A in range(1, 1 << n):
        for B in range(1, 1 << n):
            if A & B: continue
            d = sum(vals[i] for i in range(n) if A >> i & 1) - sum(vals[i] for i in range(n) if B >> i & 1)
            out.append((d > 0) - (d < 0))
    return tuple(out)


def labelings(sets, i, j, deg, Le, Lf):
    """Every map from the configuration labels (Le for agent i, Lf for agent j) to the core's goods."""
    Si, Sj = sets[i], sets[j]
    sh = set(Si) & set(Sj)
    d2 = sorted(g for g in sh if deg[g] == 2)
    common_lab = [l for l in Le if l in Lf and l not in ('g0', 'g1')]
    pe_lab = [l for l in Le if l.startswith('p')]; pf_lab = [l for l in Lf if l.startswith('p')]
    ei_lab = [l for l in Le if l not in ('g0', 'g1') and l not in common_lab and l not in pe_lab]
    fj_lab = [l for l in Lf if l not in ('g0', 'g1') and l not in common_lab and l not in pf_lab]
    pe = [g for g in Si if deg[g] == 1]; pf = [g for g in Sj if deg[g] == 1]
    if len(pe) != len(pe_lab) or len(pf) != len(pf_lab): return
    for g01 in itertools.permutations(d2, 2):
        rest_sh = [g for g in sh if g not in g01]
        if len(rest_sh) != len(common_lab): continue
        oi = [g for g in Si if g not in sh and deg[g] > 1]; oj = [g for g in Sj if g not in sh and deg[g] > 1]
        if len(oi) != len(ei_lab) or len(oj) != len(fj_lab): continue
        for cm in itertools.permutations(rest_sh):
            for a in itertools.permutations(oi):
                for b in itertools.permutations(oj):
                    mp = dict(zip(['g0', 'g1'], g01)); mp.update(zip(common_lab, cm)); mp.update(zip(ei_lab, a))
                    mp.update(zip(fj_lab, b)); mp.update(zip(pe_lab, pe)); mp.update(zip(pf_lab, pf))
                    yield mp


_PROJ = {}


def projections(uncovered, name, Le, Lf):
    if name not in _PROJ:
        U = uncovered[name]
        _PROJ[name] = ({signature([p['e'][l] for l in Le]) for p in U}, {signature([p['f'][l] for l in Lf]) for p in U})
    return _PROJ[name]


def cut_domains(sets, dom, uncovered):
    """Cut the type domains by every double edge whose configuration appears in `uncovered` (name -> list of profiles
    no reduction covers). A certified configuration has an empty list, so it empties both domains."""
    kd, deg = kinds(sets)
    dom = [list(d) for d in dom]
    rules = []
    for i, j, ki, kj, c in double_edges(sets):
        if (ki, kj, c) not in LABELS: continue
        name = config_name(ki, kj, c)
        if name not in uncovered: continue
        Le, Lf = LABELS[(ki, kj, c)]
        PE, PF = projections(uncovered, name, Le, Lf)
        for mp in labelings(sets, i, j, deg, Le, Lf):
            pos_e = [sets[i].index(mp[l]) for l in Le]; pos_f = [sets[j].index(mp[l]) for l in Lf]
            dom[i] = [v for v in dom[i] if signature([v[k] for k in pos_e]) in PE]
            dom[j] = [v for v in dom[j] if signature([v[k] for k in pos_f]) in PF]
        rules.append((name, i, j))
    return dom, rules


def main():
    recs = json.load(gzip.open(sys.argv[1], 'rt'))
    uncovered = {}
    for path in sys.argv[2:]: uncovered.update(json.load(open(path)))
    if uncovered:
        import reduce4 as R4
    by = collections.Counter(); left = collections.Counter(); prof0 = collections.Counter(); prof1 = collections.Counter()
    for r in recs:
        m = r.get('m'); by[m] += 1
        if excluded(r['sets']) is not None: continue
        left[m] += 1
        if uncovered:
            dom = r.get('domains') or [list(R4.TYPES[len(S)]) for S in r['sets']]
            p0 = 1
            for d in dom: p0 *= len(d)
            d2, _ = cut_domains(r['sets'], dom, uncovered)
            p1 = 1
            for d in d2: p1 *= len(d)
            prof0[m] += p0; prof1[m] += p1
    for m in sorted(by):
        print('m = %s: %d candidates, %d without a certified double edge' % (m, by[m], left[m]) +
              (('; their profiles %.3g -> %.3g after the domain cuts' % (prof0[m], prof1[m])) if uncovered else ''))
    print('total: %d candidates, %d left' % (sum(by.values()), sum(left.values())))


if __name__ == '__main__':
    main()
