"""The n = 4 counterexamples to OC1^max (k4/ttc.md §14), taken apart in TTC terms.

Input: the instance list of the certifier's ordinal CEGAR (branch compute/k4-oc1max-cert,
results/k4_oc1max/oc1max_cex_n4.json: one failing strict profile and maximum-matching picks per core hypergraph).
For each instance:
  - checks: is_core4, nu, no agent with two private goods (K4.MC2 class); the picks are a serial-dictatorship outcome
    (the listed order); no one-absorber completion at the picks or after any one de_free move (SAT, oc_absorb), and
    none by brute force (raw EFX0, every way to hand out the junk);
  - the want graph (i -> j: i values j's pick above its own), the frozen agents, receivers and dangerous agents;
  - every complete EFX0 allocation that value-dominates the picks (brute force over all n^m allocations), with its
    exchange shape: for each agent, the set of other agents whose picks it holds.  A de_free move gives each
    participant exactly one predecessor's base plus junk (x_0: junk plus part of B_{x_t}), so a target in which some
    agent holds the picks of two other agents cannot be reached by one move followed by a completion that keeps the
    bases;
  - the two-move repairs (de_free chains and additions, then a one-absorber completion), and the canonical-chain rule
    CC2: a chain is canonical if x_0 is dangerous (frozen and valuing junk) and x_1 values x_0's pick above its own
    base.  Reported: whether every canonical first chain can be finished by a canonical second chain, and whether some
    can.

    python3 k4/ttc/oc1max_cex_n4.py FILE.json   (the certifier's {"instances": [...]} file, or a list of
    {"sets", "vals", "order", "picks"}, such as results/k4_ttc/oc1max_cex_n5_two_private.json)"""
import sys, json, itertools, collections
import ttclib as T
import oc1max_hard as H
import core_climb as CC


def load(path):
    ds = json.load(open(path))
    return ds['instances'] if isinstance(ds, dict) else ds


def canonical(E, b, path):
    if len(path) < 2:
        return False
    D = T.dangerous_set(E, b); B = T.bundles(E, b)
    return path[0] in D and len(B[path[0]]) == 1 and \
        E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]])


def moves(E, b):
    out = {}
    for b2, p in T.iter_chains_path(E, b):
        out.setdefault(b2, p)
    return out


def analyse(k, d, C):
    sets, vals = d['sets'], d['vals']; m = 1 + max(max(s) for s in sets); n = len(sets)
    order = d['order'] if 'order' in d else d['brute_force']['example order']
    E = T.Enc(sets, vals, m); Y = tuple(T.sd(E, list(order))[0]); b = T.base_of(E, Y); B = T.bundles(E, b)
    assert list(Y) == d['picks'], (Y, d['picks'])
    print('instance %d (%s #%s): sets %s vals %s order %s picks %s' % (k, d.get('list'), d.get('idx'), sets, vals,
                                                                      order, list(Y)))
    core = CC.is_core4(CC.vmatrix(sets, vals, m))
    print('  is_core4 %s, nu %d, two private goods %s, 4-good agents %d' % (core, CC.nu(sets), CC.two_private(sets),
                                                                          sum(len(s) == 4 for s in sets)))
    M1 = moves(E, b)
    sat1 = any(T.extends_A(E, b2, 1) for b2 in M1) or T.extends_A(E, b, 1)
    bf1 = next(H.completions(E, b), None) is not None or any(next(H.completions(E, b2), None) is not None for b2 in M1)
    print('  OC1^max: one-absorber completion at the picks or after one of %d moves: SAT %s, brute force %s' % (
        len(M1), sat1, bf1))
    C['OC1^max fails (SAT and brute force)'] += (not sat1 and not bf1)
    F = T.frozen_set(E, b); D = T.dangerous_set(E, b); J = [g for g in range(m) if b[g] < 0]
    want = {i: [j for j in range(n) if j != i and E.v[i].get(Y[j], 0) > E.v[i].get(Y[i], 0)] for i in range(n)}
    print('  wants %s; frozen %s; receivers %s; dangerous %s; junk %s' % (
        want, sorted(F), [i for i in range(n) if i not in F],
        {x: {g: E.v[x][g] for g in J if E.v[x].get(g, 0) > 0} for x in sorted(D)}, J))
    starved = [i for i in range(n) if all(E.v[i].get(Y[i], 0) <= E.v[i].get(g, 0) for g in sets[i])]
    print('  agents holding their worst relevant good: %s' % starved)
    # targets: EFX0 allocations value-dominating the picks
    tg = []; owner = {Y[i]: i for i in range(n)}
    for a in itertools.product(range(n), repeat=m):
        X = [[g for g in range(m) if a[g] == i] for i in range(n)]
        if all(T.val(E, i, X[i]) >= E.v[i].get(Y[i], 0) for i in range(n)) and H.efx0(E.v, X):
            tg.append(X)
    indeg = []
    for X in tg:
        src = {i: sorted(set(owner[g] for g in X[i] if g in owner and owner[g] != i)) for i in range(n)}
        indeg.append(max(len(s) for s in src.values()))
        print('    target %s utilities %s, picks taken from %s' % (X, [T.val(E, i, X[i]) for i in range(n)], src))
    print('  %d targets; least "most other owners in one bundle" over the targets: %s' % (len(tg), min(indeg) if indeg
                                                                                          else None))
    C['least most-owners %s' % (min(indeg) if indeg else None)] += 1
    # Lemma T6 (k4/ttc.md §14.2): after one move and a completion keeping the new bases, an agent holds the picks of
    # two other agents only as an internal chain member x_j (j >= 1), whose own step takes one of them plus junk.  A
    # target is blocked if some agent holds two other picks P, Q (or more) and neither P nor Q plus all the junk the
    # agent values beats its pick.
    vj = {i: sum(E.v[i].get(g, 0) for g in J) for i in range(n)}
    blk = []
    for X in tg:
        why = None
        for i in range(n):
            P = [g for g in X[i] if g in owner and owner[g] != i]
            if len(P) >= 3 or (len(P) == 2 and all(E.v[i].get(p, 0) + vj[i] <= E.v[i].get(Y[i], 0) for p in P)):
                why = i; break
        blk.append(why)
    t6 = bool(tg) and all(w is not None for w in blk)
    print('  Lemma T6 blocks %d of %d targets (blocking agents %s): %s' % (
        sum(w is not None for w in blk), len(tg), sorted(set(w for w in blk if w is not None)),
        'no single move reaches a target (a proof, given the target list)' if t6 else 'not a T6 certificate'))
    C['Lemma T6 certifies the failure'] += t6
    # two moves
    rep = []; can_any = False; can_all = True; firsts = 0
    for b1, p1 in M1.items():
        M2 = moves(E, b1)
        good = [p2 for b2, p2 in M2.items() if T.extends_A(E, b2, 1)]
        goodc = [p2 for b2, p2 in M2.items() if canonical(E, b1, p2) and T.extends_A(E, b2, 1)]
        if good:
            rep.append((p1, canonical(E, b, p1), good, goodc))
        if canonical(E, b, p1):
            firsts += 1
            can_any |= bool(goodc); can_all &= bool(goodc)
    print('  two-move repairs (first move, canonical?, repairing second moves, canonical ones):')
    for r in rep:
        print('    ', r)
    print('  OC2^max %s; canonical first chains %d; CC2 (some canonical + canonical) %s; every canonical first chain '
          'finishes canonically %s' % (bool(rep), firsts, can_any, can_all and firsts > 0))
    C['OC2^max holds'] += bool(rep); C['CC2 holds'] += can_any; C['every canonical first chain works'] += (
        can_all and firsts > 0)
    C['every repairing first move is canonical'] += all(r[1] for r in rep) and bool(rep)


if __name__ == '__main__':
    print('$ python3 k4/ttc/oc1max_cex_n4.py', *sys.argv[1:])
    ds = load(sys.argv[1])
    C = collections.Counter()
    for k, d in enumerate(ds):
        analyse(k, d, C)
    print('instances', len(ds))
    for key in sorted(C):
        print(key, C[key])


def fixed_point_min(E, b, b2, path):
    """k4/ttc.md §11's fixed point with a minimal danger set: x_0 dangerous takes an inclusion-minimal improving set
    of junk (and nothing from a base), every x_i (i >= 1) takes exactly x_{i-1}'s base (a pure want path), and x_t is
    unfrozen (a receiver)"""
    if len(path) < 2:
        return False
    B = T.bundles(E, b); D = T.dangerous_set(E, b); F = T.frozen_set(E, b)
    x0 = path[0]
    if x0 not in D or path[-1] in F:
        return False
    H0 = [g for g in range(E.m) if b2[g] == x0]
    if any(b[g] >= 0 for g in H0):
        return False
    v0 = T.val(E, x0, B[x0])
    if any(T.val(E, x0, S) > v0 for r in range(1, len(H0)) for S in itertools.combinations(H0, r)):
        return False
    return all(sorted(g for g in range(E.m) if b2[g] == path[i]) == sorted(B[path[i - 1]]) for i in range(1, len(path)))


def fp_report(ds):
    C = collections.Counter()
    for k, d in enumerate(ds):
        sets, vals = d['sets'], d['vals']; m = 1 + max(max(s) for s in sets)
        order = d['order'] if 'order' in d else d['brute_force']['example order']
        E = T.Enc(sets, vals, m); Y = tuple(T.sd(E, order)[0]); b = T.base_of(E, Y)
        fps = [(b1, p1) for b1, p1 in moves(E, b).items() if fixed_point_min(E, b, b1, p1)]
        ok = [p1 for b1, p1 in fps if any(T.extends_A(E, b2, 1) for b2 in moves(E, b1))]
        okfp = [p1 for b1, p1 in fps if any(fixed_point_min(E, b1, b2, p2) and T.extends_A(E, b2, 1)
                                            for b2, p2 in moves(E, b1).items())]
        print('  instance %d: %d minimal fixed-point first chains %s; finished by some move: %d; by a minimal fixed point: '
              '%d' % (k, len(fps), [p for _, p in fps], len(ok), len(okfp)))
        C['instances'] += 1; C['some minimal fixed point exists'] += bool(fps)
        C['every minimal fixed point is finished by one more move'] += bool(fps) and len(ok) == len(fps)
        C['some minimal fixed point is finished by one more move'] += bool(ok)
        C['two minimal fixed points suffice'] += bool(okfp)
    for key in sorted(C):
        print(' ', key, C[key])


if __name__ == '__main__':
    print('minimal fixed points (§11) as first moves:')
    fp_report(load(sys.argv[1]))
