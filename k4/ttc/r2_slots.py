"""Where the junk goes in R2* completions (k4/ttc.md §14.6, step 4).  At every hard perfect start with >= 2 receivers
(n = 6 sweep sample as r2_shape.py, or a walk around FILE's instances), find canonical chains (x_0 dangerous, x_1
wants y_{x_0}) ending at a receiver z after which some completion gives every agent at most one junk good, and
classify the agents that receive a junk good: unwanted single-good holders at the new state (slots that need no
compensation), x_0, frozen singles (wanted at the new state: Lemma 1 / M^c frozen slots), or other multi-good agents.
Also records |J'| against the number of unwanted holders + 1.  Reports whether, for every start, some such chain
needs no frozen slot.

    python3 k4/ttc/r2_slots.py sweep N4[,N4..] STRIDE R SEED | walk FILE.json STEPS SEED"""
import sys, os, json, itertools, collections, time, random, multiprocessing as mp
import ttclib as T
import oc1max_n6 as O
import oc1max_cex_n4 as X
import core_climb as CC
import r2_shape as R
from pysat.solvers import Cadical153


def model_none(E, b2, forbid_frozen=False):
    """a completion keeping b2 with at most one junk good per agent (optionally none to wanted single-good agents)"""
    cl = list(E.cl); J = [g for g in range(E.m) if b2[g] < 0]
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
        if b2[g] >= 0:
            cl.append([E.x[g][b2[g]]])
    for i in range(E.n):
        for g, h in itertools.combinations(J, 2):
            cl.append([-E.x[g][i], -E.x[h][i]])
    if forbid_frozen:
        for i in T.frozen_set(E, b2):
            for g in J:
                cl.append([-E.x[g][i]])
    S = Cadical153(bootstrap_with=cl)
    if not S.solve():
        S.delete(); return None
    mod = set(l for l in S.get_model() if l > 0); S.delete()
    return [[g for g in range(E.m) if E.x[g][i] in mod] for i in range(E.n)]


def test_start(E, b, C, out, info):
    F = T.frozen_set(E, b); U = [i for i in range(E.n) if i not in F]
    if len(U) < 2:
        return
    D = T.dangerous_set(E, b); B = T.bundles(E, b)
    C['hard starts with >= 2 receivers'] += 1
    found = False; found_nf = False; kinds = collections.Counter(); cnt = None
    for b2, path in T.iter_chains_path(E, b):
        if not (len(path) >= 2 and path[0] in D and path[-1] in U and
                E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]])):
            continue
        Xc = model_none(E, b2)
        if Xc is None:
            continue
        found = True
        B2 = T.bundles(E, b2); F2 = T.frozen_set(E, b2); J2 = [g for g in range(E.m) if b2[g] < 0]
        hold = [i for i in range(E.n) if len(B2[i]) <= 1 and i not in F2]
        if cnt is None:
            cnt = (len(J2), len(hold))
            for i in range(E.n):
                if any(g in J2 for g in Xc[i]):
                    kinds['x_0' if i == path[0] else ('unwanted holder' if i in hold else
                          ('frozen single' if len(B2[i]) == 1 else 'multi-good agent'))] += 1
        if not found_nf and model_none(E, b2, forbid_frozen=True) is not None:
            found_nf = True
        if found_nf:
            break
    if not found:
        C['NO R2* CHAIN'] += 1; out.append(('NO R2* CHAIN', info)); return
    for k, v in kinds.items():
        C['  first R2* completion: junk goods to %s' % k] += v
    C['  first R2* chain: |J\'| - (unwanted holders + 1) = %d' % (cnt[0] - cnt[1] - 1)] += 1
    C['  some R2* chain needs no frozen slot' if found_nf else '  EVERY R2* chain needs a frozen slot'] += 1
    if not found_nf:
        out.append(('needs frozen slot', info))


R.test_start = test_start   # reuse r2_shape's drivers (job, walk_one, run) with this test

if __name__ == '__main__':
    print('$ python3 k4/ttc/r2_slots.py', *sys.argv[1:], flush=True)
    t0 = time.time(); a = sys.argv[1:]
    if a[0] == 'sweep':
        n4s = [int(x) for x in a[1].split(',')]; stride = int(a[2]); Rr = int(a[3]); seed = int(a[4]); tasks = []
        for n4 in n4s:
            k = 0
            for m in range(4, 3 * O.N + 1):
                for sets in O.S4.cores(O.N, m, n4 == O.N, None if n4 == O.N else n4):
                    k += 1
                    if k % stride == 0 and CC.nu(sets) == O.N:
                        tasks.append((m, sets, Rr, seed * 1000003 + len(tasks)))
        Ctot = R.run(tasks, R.job)
    else:
        ds = X.load(a[1]); steps = int(a[2]); seed = int(a[3])
        Ctot = R.run([(d, steps, seed * 7919 + k) for k, d in enumerate(ds)], R.walk_one)
    for k in sorted(Ctot):
        print(k, Ctot[k])
    print('time %.0f s' % (time.time() - t0), flush=True)
