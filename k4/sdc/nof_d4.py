"""Proposition D4 (k4/sdc.md §16): the k = 4 form of Proposition D3, deferral = rotation.  For every plain neediest-first
R1 run pi (--nor1: without R1 priority) whose picks Y do not extend, let P be LB4r's state after need-shrinking upgrades.  For a frozen agent k of P,
let c be the displacement chain of Lemma DC for moving k to the end of pi, and y the pick of k in SD(pi_k).  The
deferral is *a rotation* if
  (R1) c = k, j_1, ..., j_t is a need chain of P (RotStep: every agent but the last FrozenAt, the pick of each needed
       by the next, the last not FrozenAt) with no marked agent, and
  (R2) y lies in R_k cap (J + base(j_t)), the goods a rotation may give k.
Then for every O with y in O and v_k(O) > v_k(Y_k) that passes RotChecks, the rotated state P' = rotate(P, c, O) holds
SD(pi_k)'s picks inside its bases, so every LB4r Output of P' completes SD(pi_k) to an EFX0 allocation (Theorem 1'_4).
Counts: failures where some deferral is a rotation; where some rotation's P' has an Output (D4 certifies the repair);
where the repairing deferral is not a rotation, and why.

    python3 k4/sdc/nof_d4.py screen|suite|cores:FILES N SEED [--nor1]   (--nor1: the order without R1 priority)"""
import sys, os, json, gzip, random, itertools, collections
import _paths
from sdclib import Enc
from sdc_need import instances, rule_order
from sdc_orders import completable, sd
from blocks4 import M, RM


def dc_chain(E, pi, Y, k):
    """Lemma DC: chain of agents and the final hole for moving k to the end of pi"""
    pos = {a: t for t, a in enumerate(pi)}; chain = [k]; h = Y[k]; cur = k
    while h is not None:
        nxt = None
        for a in pi[pos[cur] + 1:]:
            if a == k: continue
            va = E.v[a].get(h, 0)
            if va > 0 and (Y[a] is None or va > E.v[a][Y[a]]):
                nxt = a; break
        if nxt is None: break
        chain.append(nxt); h = Y[nxt]; cur = nxt
    return chain, h


if __name__ == '__main__':
    R1 = '--nor1' not in sys.argv
    if not R1: sys.argv.remove('--nor1')
    src = sys.argv[1]; C = collections.Counter(); shown = 0
    print('$ python3 k4/sdc/nof_d4.py', *sys.argv[1:], '' if R1 else '--nor1')
    if src.startswith('cores:'):
        N, seed = int(sys.argv[2]), int(sys.argv[3]); rng = random.Random(seed); items = []
        cwd = os.getcwd(); os.chdir(_paths.DE4)
        from de4lib import random_profile
        os.chdir(cwd)
        cores = []
        for fn in src[6:].split(','):
            cores += [c['sets'] for c in json.load(gzip.open(os.path.join(_paths.ROOT, 'results', fn)))['cores']]
        for t in range(N):
            sets = rng.choice(cores); items.append(('r%d' % t, sets, random_profile(sets, rng), 1 + max(max(x) for x in sets)))
    else:
        items = instances(src)
    for name, sets, vals, m in items:
        if len(sets) > 9: continue
        E = Enc(sets, vals, m)
        Y, pi = rule_order(E, 'need2', R1)
        if completable(E, Y): continue
        v = [[0] * m for _ in sets]
        for i, (S, V) in enumerate(zip(sets, vals)):
            for g, x in zip(S, V): v[i][g] = x
        inst = M.Inst(v); n = inst.n
        base = [-1] * m; pick = [-1] * n
        for i, g in enumerate(Y):
            if g is not None: base[g] = i; pick[i] = g
        s = (tuple(base), tuple(pick), tuple([False] * n)); s, ups = M.up_run(inst, s, 'shrink')
        needs = M.all_needs(inst, s); NA = M.NA_of(needs); fa = M.frozen_at(inst, s, NA)
        C['failures'] += 1
        works = {o for o in pi if completable(E, sd(E, [i for i in pi if i != o] + [o])[0])}
        rot_any = cert_any = False; why = collections.Counter()
        for k in pi:
            if not fa[k]: continue
            c, hole = dc_chain(E, pi, Y, k)
            Yk = sd(E, [i for i in pi if i != k] + [k])[0]; y = Yk[k]
            ok_chain = len(c) >= 2 and all(fa[c[i]] for i in range(len(c) - 1)) and not fa[c[-1]] and \
                all(s[1][c[i]] >= 0 and s[1][c[i]] in needs[c[i + 1]] for i in range(len(c) - 1)) and not any(s[2][x] for x in c)
            if not ok_chain:
                why['k%s: DC chain not a need chain of P (or marked agent on it)' % ('works' if k in works else 'fails')] += 1; continue
            pool = [g for g in range(m) if v[k][g] > 0 and (s[0][g] == -1 or s[0][g] == c[-1])]
            if y is None or y not in pool:
                why['k%s: pick of k outside J + base(last)' % ('works' if k in works else 'fails')] += 1; continue
            rot_any = True
            rest = [g for g in pool if g != y]; got = False
            for r in range(len(rest) + 1):
                for Q in itertools.combinations(rest, r):
                    O = (y,) + Q
                    if not sum(v[k][g] for g in O) > v[k][s[1][k]]: continue
                    s2 = M.rotate(s, c, O)
                    if not M.rot_checks(inst, s2): continue
                    if M.any_output(inst, s2, 'bundle'):
                        got = True; break
                if got: break
            if got:
                cert_any = True
                C['certified k is frozen-threatened by J? %s' % any(True for _ in [0])] += 0
            else:
                why['k%s: rotation, but no rotated state has an Output' % ('works' if k in works else 'fails')] += 1
        C['some deferral is a rotation (R1, R2)'] += rot_any
        C['D4 certifies a repair (rotated state has an LB4r Output)'] += cert_any
        if not cert_any:
            for w, c_ in why.items(): C['uncertified failure, ' + w] += c_
            if shown < 6:
                shown += 1; print('UNCERTIFIED', name, 'sets', sets, 'vals', vals, 'pi', pi, 'Y', Y, 'ups', ups, 'works', sorted(works), dict(why))
    for k in sorted(C, key=str):
        if C[k]: print(k, C[k])
