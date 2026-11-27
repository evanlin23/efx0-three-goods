"""Conjecture RKMAX (rank-maximal start; k4/sdc.md §31 end and ledger K4.SDC.RKMAX on the coordinator's branch) fails at
k = 5 with three agents (k4/ksens.md §8).  The witnesses: rkcegar.py's FAIL profiles on the 13 n = 3 hypergraphs where
OC1^max fails (results/k4_ksens/rkcegar_k5_n3.log), and the 15 known failing starts of rf_replay.py.

For each profile, from the definitions:
- every SD vector (all n! orders, brute.py), the maximum-matching ones (nu, maxmatch.py), and their rank signatures
  sigma = (#rank 1, ..., #rank k), rank_i = 1 + the number of i's relevant goods valued above its pick;
- OC1 at each sigma-maximal vector (one-absorber completion at the picks or after one chain, official rule) by two
  checkers: brute force (brute.py: every chain from the definition, every complete allocation) and SAT (ocsat.py;
  its chains allow empty passes, which only adds moves, so a SAT "no" is a "no" for the official rule too).
RKMAX fails at a profile when some sigma-maximal maximum-matching vector fails OC1 (both checkers).  The weaker
"some sigma-maximal vector satisfies OC1" (which still gives OC1^exists-max) is reported too.

    python3 k4/ksens/refute_rkmax_k5.py"""
import json, itertools, time
import _paths
import brute, ocsat, rf_replay
from maxmatch import nu


def sig(sets, vals, Y, k):
    s = [0] * k
    for i, g in enumerate(Y):
        if g is None: continue
        v = dict(zip(sets[i], vals[i])); s[sum(1 for h in sets[i] if v[h] > v[g])] += 1
    return tuple(s)


def check(name, sets, vals):
    n = len(sets); m = 1 + max(max(s) for s in sets); k = max(map(len, sets))
    I = brute.Inst(sets, vals, m); O = ocsat.OC(sets, vals, m); v = nu(sets, vals)
    vecs = {}
    for o in itertools.permutations(range(n)): vecs.setdefault(tuple(I.sd(o)), []).append(o)
    mx = {Y: sig(sets, vals, Y, k) for Y in vecs if sum(g is not None for g in Y) == v}
    top = max(mx.values()); best = [Y for Y, s in mx.items() if s == top]
    res = {}
    for Y in best:
        b = ocsat.bases_of(Y, n)
        sat = O.holds(b, chain='none', A=1) or O.holds(b, chain='any', A=1)
        res[Y] = (rf_replay.oc1(I, Y, n), sat)
    O.close()
    fails = [Y for Y, (bf, sat) in res.items() if bf is None and not sat]
    disagree = [Y for Y, (bf, sat) in res.items() if (bf is None) == sat]
    print('%s: sigma-max %s over %d maximum-matching SD vectors; sigma-maximal vectors and OC1 [brute, SAT]: %s; RKMAX %s; '
          'some sigma-maximal vector OC1: %s%s' % (name, top, len(mx), {str(Y): res[Y] for Y in best},
          'FAILS' if fails else 'holds', len(fails) < len(best), '; CHECKER DISAGREEMENT %s' % disagree if disagree else ''),
          flush=True)
    return bool(fails), len(fails) < len(best), bool(disagree)


if __name__ == '__main__':
    print('$ python3 k4/ksens/refute_rkmax_k5.py', flush=True); t0 = time.time(); cases = []
    for l in open('../../results/k4_ksens/rkcegar_k5_n3.log'):
        if l.startswith('n3_') and 'FAIL' in l: name, S = l.split()[0], json.loads(l[l.index('[['):l.index(']]') + 2])
        if l.strip().startswith('{"vals"'): cases.append(('rkcegar ' + name, S, json.loads(l)['vals']))
    for l in open('../../results/k4_ksens/kcegar_k5_n3_D1.log'):
        if '"result": "FAIL"' in l: r = json.loads(l); cases.append(('kcegar ' + r['name'], r['sets'], r['recheck']['vals']))
    import refute_rd_k5 as RD, fam_ladder
    cases.append(('RD5', RD.SETS, RD.VALS)); s, v_, m = fam_ladder.clean(3, 2, 4); cases.append(('PW5', s, v_))
    F = W = Dg = 0
    for name, S, V in cases:
        f, w, dg = check(name, S, V); F += f; W += w; Dg += dg
    print('profiles %d: RKMAX fails on %d; some sigma-maximal vector satisfies OC1 on %d; checker disagreements %d (%.0f s)'
          % (len(cases), F, W, Dg, time.time() - t0))
