#!/usr/bin/env python3
"""Replays the failed routes of proof/k4-strategy (k4/strategy.md; attempts/k4-strat-*.md). Each check prints its verdict
with two implementations where they exist and "confirmed" when the failure reproduces.
usage: python3 attempts/k4_strat_attempts.py"""
import os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'k4', 'suite'))
import json
import model as M, predicates as PR, triples as T, ext

ok_all = True


def say(name, ok, detail=''):
    global ok_all
    ok_all &= ok
    print('%-58s %s  %s' % (name, 'confirmed' if ok else 'NOT REPRODUCED', detail))


def load(i):
    d = json.load(open(os.path.join(ROOT, 'k4', 'suite', 'instances', i + '.json'))); d.setdefault('m', 1 + max(g for S in d['sets'] for g in S)); return d


# 1. COUNT (attempts/k4-strat-count.md): no pool-optimal configuration has r' > |D|, yet C4min holds
d = load('count-n3m8')
a, b = PR.count_suite(d), PR.count_gap(d)
c1, c2 = PR.cfg_suite(d), PR.cfg_gap(d)
say('COUNT fails at n = 3, m = 8 (count-n3m8)', a[0] is False and b[0] is False and c1[0] and c2[0],
    'COUNT suite/gap: %s/%s; C4min configuration form suite/gap: %s/%s' % (a[0], b[0], c1[0], c2[0]))

# 2. triple spaces (attempts/k4-strat-triples.md): Pareto-maxima of P_bt / P_low not completable
for iid in ('hall-local3', 'hall-bt4'):
    d = load(iid); I = M.Inst(d['sets'], d['vals'])
    for mode in ('bt', 'low'):
        S = T.TSpace(I, mode)
        bad = [(Bs, NA) for Bs, NA in S.pareto_max() if not S.removal_only(Bs)[0]]
        full = [S.completable_full(Bs)[0] for Bs, NA in bad]
        say('P_%s: a Pareto-maximum is not completable (%s)' % (mode, iid), bool(bad) and not any(full),
            'bases %s, completable with any completion: %s' % ([[sorted(M.bits(B)) for B in Bs] for Bs, _ in bad], full))
d = load('hall-local3'); I = M.Inst(d['sets'], d['vals'])
say('  local3: the triple {4,5,6} of agent 1 threatens agent 2 holding {3}', I.threat(2, M.mask([4, 5, 6]), I.val(2, M.mask([3]))),
    'agent 2 values 4, 5, 6 at 3, 5, 6 and 3 at 7')

# 3. PS_W (attempts/k4-strat-psw.md): twins. I: agent 0 values {0, 2, 3} at (2, 5, 4), agent 1 values {1, 2, 3} at (2, 5, 4)
sets, vals = [[0, 2, 3], [1, 2, 3]], [[2, 5, 4], [2, 5, 4]]
I = M.Inst(sets, vals)
say('  twins: I is a k = 4 core (in fact a k = 3 core)', not I.core_violations(), str(I.core_violations()))
J = M.Inst([[2, 3], [2, 3]], [[5, 4], [5, 4]], m=4)           # I minus both private goods (goods 0, 1 kept as junk-free labels)
Jb = M.Inst([[0, 2, 3], [2, 3]], [[2, 5, 4], [5, 4]], m=4)    # I minus the private good 1 of agent 1
S = ext.induct_sat()
def ps2(sets_, vals_, m, W):
    V = [[0] * m for _ in sets_]
    for i, (Sg, t) in enumerate(zip(sets_, vals_)):
        for g, x in zip(Sg, t): V[i][g] = x
    Mo = S.Model(V, list(range(len(sets_))), list(range(m)))
    extra = [c for w in W for c in Mo.unenvied(w)]
    return Mo.solve(extra=extra)
r1 = (J.efx0_search(unenvied=[0, 1]), ps2([[2, 3], [2, 3]], [[5, 4], [5, 4]], 4, [0, 1]))
r2 = (Jb.efx0_search(unenvied=[0, 1]), ps2([[0, 2, 3], [2, 3]], [[2, 5, 4], [5, 4]], 4, [0, 1]))
r3 = (I.efx0_search(), I.efx0_search(unenvied=[0]), I.efx0_search(unenvied=[1]))
say('PS_{0,1}(I - {0, 1}) fails (both agents stripped)', r1[0] is None and r1[1] is None, 'suite/induct: %s/%s' % r1)
say('PS_{0,1}(I - {1}) holds, and TARGET(I), PS(I, 0), PS(I, 1) hold', all(x is not None for x in r2 + r3), '')

print('ALL CONFIRMED' if ok_all else 'SOMETHING DID NOT REPRODUCE')
