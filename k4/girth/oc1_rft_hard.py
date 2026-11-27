"""Corollary RF-T''s facts (F1)-(F3) from the hardness of Y (the open item of k4/girth.md section 7): counterfactual
sampling.  Random strict balanced order types (k4/girth/sources.domains) on the pure n = 5 cores with m = 8 (so
|J| = 3, as in RF-T).  For every order sigma whose picks Y are perfect with exactly one receiver u, Y' = SD(u, then
sigma - u), and RF-T's setting at Y' (RF path u = x0, ..., x_l = d, l >= 2, d takes a junk good g of Y; Y' has the
one receiver d and D_T' empty; a valid trade p, j: p pick-dangerous at Y' holding Y_p, j in J valued by p,
v_p({g, j}) > v_p(Y_p), v_d(Y_p) > v_d(g), J' - {j} = {Y_u, z}), record (F1), (F2), (F3) per trade, and whether Y
is an OC1 failure (k4/sdc/oc1_mc2_rand.Inst.check, raw).  For the starts where some fact fails at every trade, what
repairs Y: the first repairing completion or official move, described by roles at Y (k4/girth/oc1_demote.describe_move).
The claim to test: Y an OC1 failure => (F1)-(F3) at some trade.  EVIDENCE.

    python3 k4/girth/oc1_rft_hard.py PROFILES_PER_CORE SEED [JOBS]
"""
import collections
import itertools
import json
import multiprocessing as mp
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_r2n5 import path_from  # noqa: E402
from oc1_rf_owner import owner_ok  # noqa: E402
from oc1_demote import describe_move  # noqa: E402


def facts(I, Y, Y2, u, path, J, J2):
    """per valid RF-T trade (p, j): (F1, F2, F3, F1 detail)"""
    n = len(Y)
    v = I.v
    d = path[-1]
    rl2, _ = roles(I.sets, I.vals, list(Y2))
    out = []
    for p in range(n):
        if rl2[p] != 'Dp' or Y2[p] != Y[p]:
            continue
        for j in J2:
            if j not in v[p] or j not in J:
                continue
            if not (I.V(p, [Y2[d], j]) > I.V(p, [Y2[p]]) and I.V(d, [Y2[p]]) > I.V(d, [Y2[d]])):
                continue
            rest = [g for g in J2 if g != j]
            if len(rest) != 2 or Y[u] not in rest:
                continue
            F1 = v[d].get(Y[p], 0) > v[d][Y[d]]
            F2 = all(not (v[i].get(Y[d], 0) > v[i].get(Y[i], 0)) for i in range(n) if i not in path)
            F3 = all(i in (p, d, u) for i in range(n) if Y[p] in v[i])
            out.append((p, j, F1, F2, F3))
    return out


def canonical_X(I, Y, Y2, u, path, J2, p, j):
    z = [g for g in J2 if g not in (j, Y[u])][0]
    X = [[g] for g in Y2]
    X[p] = [Y2[path[-1]], j]
    X[path[-1]] = [Y2[p], Y[u]]
    X[path[-2]] = [Y2[path[-2]], z]
    return X


def why_X_fails(I, Y, Y2, u, path, J2, p, j):
    X = canonical_X(I, Y, Y2, u, path, J2, p, j)
    n = len(Y)
    d, xl1 = path[-1], path[-2]
    v = I.v
    out = []
    lab = lambda i: 'd' if i == d else 'u' if i == u else 'p' if i == p else (
        'x%d' % path.index(i) + ('=x_(l-1)' if i == xl1 else '') if i in path else 'off-path q')
    for i in range(n):
        if i != xl1 and v[i].get(Y[d], 0) > I.V(i, X[i]):
            out.append('(W-d) fails at %s' % lab(i))
        if i != d and v[i].get(Y[p], 0) > I.V(i, X[i]):
            out.append('(W-p) fails at %s' % lab(i))
    return out or ['X EFX0']


def two_chain(I, Y, Y2, path, p, j):
    """p takes {Y2_d = g, j}, q takes Y_p, for q a (W-p) violator; then a one-absorber completion"""
    n = len(Y)
    d = path[-1]
    g = Y2[d]
    res = 'no (W-p) violator'
    for q in range(n):
        if q in (p, d) or not I.v[q].get(Y[p], 0) > I.v[q].get(Y[q], 0):
            continue
        st = [[x] for x in Y]
        st[p] = [g, j]
        st[q] = [Y[p]]
        if I.one_absorber(st):
            return 'works'
        res = 'fails'
    return res


def completions_after_pu(I, Y, Y2, u, path, J, p, j):
    """after the chain p takes {g, j}, u takes Y_p: every placement of the free goods {Y_u, z} (to one agent, to two
    agents, or one/both to nobody is not allowed) that is EFX0, labelled by path position"""
    n = len(Y)
    d = path[-1]
    g = Y2[d]
    z = [x for x in J if x not in (g, j)][0]
    st = [[x] for x in Y]
    st[p] = [g, j]
    st[u] = [Y[p]]
    lab = lambda i: 'd' if i == d else 'u' if i == u else 'p' if i == p else (
        'x%d' % path.index(i) if i in path else 'q')
    out = []
    for a in range(n):
        for b in range(n):
            B = [list(x) for x in st]
            B[a].append(Y[u])
            B[b].append(z)
            if I.efx0(B):
                out.append('Y_u to %s, z to %s' % (lab(a), lab(b)))
    return out or ['no completion']


def p_tail_chain_repairs(I, Y, J, p):
    """some official move in which p gives up Y_p for junk (plus possibly the freed pick of the head), followed by a
    one-absorber completion"""
    base = [[g] for g in Y]
    for st in I.moves(base):
        st = [list(b) for b in st]
        if Y[p] in st[p] or not set(st[p]) - set(J) <= set(Y):
            continue
        if any(g in J for g in st[p]) and I.one_absorber(st):
            return True
    return False


def repair(I, Y, rl, J):
    base = [[g] for g in Y]
    n = len(Y)
    for a in [None] + list(range(n)):
        if (a is None or len(J) >= 2) and owner_ok(I, base, a):
            return 'picks complete, owner ' + ('none' if a is None else rl[a])
    for st in I.moves(base):
        st = [list(b) for b in st]
        if I.one_absorber(st):
            # describe_move tags a one-agent path as (d); here that agent is Y's receiver u
            return 'move: ' + describe_move(base, st, rl, sorted(J), [rl.index('U')]).replace('U(d)', 'U(u)')
    return 'OC1 fails'


def job(task):
    from sources import domains
    idx, sets, m, K, seed = task
    rng = random.Random(seed * 100019 + idx)
    doms = domains(sets, m)
    n = len(sets)
    R = [set(s) for s in sets]
    C = collections.Counter()
    ex = []
    allo = list(itertools.permutations(range(n)))
    for t in range(K):
        ds = [rng.choice(D) for D in doms]
        vals = [[d[g] for g in sorted(d)] for d in ds]
        v = [dict(d) for d in ds]
        I = Inst(sets, vals)
        seen = set()
        for o in allo:
            Y = sd(R, v, o)
            if None in Y:
                continue
            rl, J = roles(sets, vals, list(Y))
            if rl.count('U') != 1:
                continue
            u = rl.index('U')
            Y2 = sd(R, v, [u] + [a for a in o if a != u])
            if None in Y2 or (Y, Y2) in seen:
                continue
            seen.add((Y, Y2))
            C['stage 1: one receiver at Y, Y\' perfect'] += 1
            path = path_from(Y, Y2, J, u)
            d = path[-1]
            if len(path) < 3 or Y2[d] not in J:
                continue
            C['stage 2: path length >= 2, d takes junk'] += 1
            rl2, J2 = roles(sets, vals, list(Y2))
            if rl2.count('U') != 1 or rl2[d] != 'U' or rl2.count('DT'):
                continue
            C['stage 3: DEMOTE-0 at Y\''] += 1
            fs = facts(I, Y, Y2, u, path, J, J2)
            if not fs:
                continue
            C['RF-T settings (Y, Y\')'] += 1
            C['structure: u is last in sigma, d is last in sigma\' (must be all)'] += (o[-1] == u and
                                                                                      o[-2] == d)
            xs = [canonical_X(I, Y, Y2, u, path, J2, f[0], f[1]) for f in fs]
            for f in fs:
                C['every trade: d values j: %s' % (f[1] in I.v[d])] += 1
                C['every trade: u values a junk good of Y: %s' % any(x in I.v[u] for x in J)] += 1
            xok = any(I.efx0(X) for X in xs)
            C['canonical X EFX0 at some trade: %s' % xok] += 1
            if not xok:
                for f in fs:
                    for key in why_X_fails(I, Y, Y2, u, path, J2, f[0], f[1]):
                        C['X fails, by trade: ' + key] += 1
                    C['X fails: the chain "p takes {g, j}, q takes Y_p", q a (W-p) violator, then completion: %s' % (
                        two_chain(I, Y, Y2, path, f[0], f[1]))] += 1
                kinds = set(k for f in fs for k in why_X_fails(I, Y, Y2, u, path, J2, f[0], f[1]))
                if kinds == {'(W-d) fails at d'}:
                    b0 = [[g] for g in Y]
                    if I.one_absorber(b0):
                        C['only (F1\') fails: picks complete'] += 1
                    else:
                        mv = sorted({describe_move(b0, [list(x) for x in st], rl, sorted(J), [rl.index('U')]).replace(
                            'U(d)', 'U(u)') for st in I.moves(b0) if I.one_absorber([list(x) for x in st])})
                        C['only (F1\') fails; shortest repairing move: ' + min(mv, key=len)] += 1
                        C['only (F1\') fails; some repairing move has p taking {g, j} and u taking Y_p: %s' % any(
                            'U(u) takes {pick of DT}' in m for m in mv)] += 1
                        for f in fs:
                            pp, jj = f[0], f[1]
                            gg = Y2[d]
                            zz = [x for x in J if x not in (gg, jj)][0]
                            v = I.v
                            for nm, ag in (('u', u), ('d', d)):
                                C['only (F1\') fails; %s values: %s' % (nm, ','.join(
                                    k for k, x in (('g', gg), ('j', jj), ('z', zz), ('Y_u', Y[u]), ('Y_p', Y[pp]))
                                    if x in v[ag]))] += 1
                            C['only (F1\') fails; u wants Y_p at Y: %s' % (v[u].get(Y[pp], 0) > v[u][Y[u]])] += 1
                            XA = [[gg, jj, Y[u]] if i == pp else [Y[pp], zz] if i == u else [Y[i]] for i in range(n)]
                            C['only (F1\') fails; X_A = (p: {g, j, Y_u}, u: {Y_p, z}) EFX0: %s' % I.efx0(XA)] += 1
                            lab = lambda i: 'd' if i == d else 'u' if i == u else 'p' if i == pp else (
                                'x%d' % path.index(i) if i in path else 'q')
                            for i in range(n):
                                for k2 in (pp, u):
                                    if k2 != i and I.V(i, XA[k2]) - min(v[i].get(h, 0) for h in XA[k2]) > I.V(i, XA[i]):
                                        C['only (F1\') fails; X_A fails: %s envies the bundle of %s' % (
                                            lab(i), lab(k2))] += 1
                        for f in fs:
                            for key in completions_after_pu(I, Y, Y2, u, path, J, f[0], f[1]):
                                C['only (F1\') fails; after "p takes {g, j}, u takes Y_p": ' + key] += 1
                b = [[g] for g in Y]
                rep = ('picks complete' if I.one_absorber(b) else
                       'a chain with tail p' if any(p_tail_chain_repairs(I, Y, J, f[0]) for f in fs) else
                       'another official move' if I.check(Y) == 'one move repairs' else 'NOTHING (Y fails)')
                C['X fails at every trade; Y repaired by: ' + rep] += 1
            ok = any(f[2] and f[3] and f[4] for f in fs)
            fail = I.check(Y) == 'OC1 fails'
            C['Y an OC1 failure: %s; F1-F3 at some trade: %s' % (fail, ok)] += 1
            for name, k in (('F1', 2), ('F2', 3), ('F3', 4)):
                C['Y an OC1 failure: %s; %s at some trade: %s' % (fail, name, any(f[k] for f in fs))] += 1
            if fail and not ok:
                C['COUNTEREXAMPLE: a failure without F1-F3'] += 1
                if len(ex) < 3:
                    ex.append(dict(idx=idx, sets=sets, vals=vals, order=list(o), Y=list(Y), Y2=list(Y2), u=u,
                                   path=path, facts=fs))
            if not fail:
                for name, k in (('F1', 2), ('F2', 3), ('F3', 4)):
                    if not any(f[k] for f in fs):
                        C['not a failure, %s at no trade; repaired by: %s' % (name, repair(I, Y, rl, J))] += 1
    return C, ex


def main():
    K, seed = int(sys.argv[1]), int(sys.argv[2])
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    print('$ python3 k4/girth/oc1_rft_hard.py', *sys.argv[1:], flush=True)
    from sources import cores
    tasks = [(idx, sets, m, K, seed) for f, idx, sets, m in cores(5, pure=True) if m == 8]
    print('cores (pure, n = 5, m = 8):', len(tasks), flush=True)
    C = collections.Counter()
    E = []
    with mp.Pool(jobs) as pool:
        for c, e in pool.imap_unordered(job, tasks, chunksize=10):
            C.update(c)
            E += e
    for k in sorted(C):
        print('   %-120s %7d' % (k, C[k]))
    for e in E[:6]:
        print('CASE', json.dumps(e))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
