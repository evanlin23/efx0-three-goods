"""R2 step 4 through Lemma M^c (k4/ttc.md §14.6).  At every hard perfect start with >= 2 receivers, for the canonical
chains (x_0 dangerous, x_1 wants y_{x_0}) ending at a receiver z, test the state after the chain with the compensated
matching model of Lemma M^c (proof/k4-oc1max-multi, k4/oc1max_multi/mc.py, commit 3d157f3), with max_rest = 1 (the
owner receives at most one junk good, so every agent at most one) and owner x_0, z, or another receiver.  M^c assumes
(G2) (no junk good is wanted); states where (G2) fails are counted separately.

Needs the other workstream's code on the path: MC_DIR=<checkout of proof/k4-oc1max-multi>/k4/oc1max_multi.

    MC_DIR=... python3 k4/ttc/r2_mc.py sweep N4[,N4..] STRIDE R SEED | walk FILE.json STEPS SEED"""
import sys, os, json, itertools, collections, time
sys.path.insert(0, os.environ.get('MC_DIR', '.'))
import ttclib as T
import oc1max_n6 as O
import oc1max_cex_n4 as X
import core_climb as CC
import r2_shape as R
import mc as MC
from mmlib import Inst


def test_start(E, b, C, out, info):
    F = T.frozen_set(E, b); U = [i for i in range(E.n) if i not in F]
    if len(U) < 2:
        return
    D = T.dangerous_set(E, b); B = T.bundles(E, b)
    I = Inst(info['sets'], info['vals'], E.m)
    C['hard starts with >= 2 receivers'] += 1
    ok = collections.Counter(); g2fail = 0; chains = 0
    for b2, path in T.iter_chains_path(E, b):
        if not (len(path) >= 2 and path[0] in D and path[-1] in U and
                E.v[path[1]].get(B[path[0]][0], 0) > T.val(E, path[1], B[path[1]])):
            continue
        chains += 1
        B2 = tuple(tuple(T.bundles(E, b2)[i]) for i in range(E.n))
        if not MC.g2(I, B2):
            g2fail += 1; continue
        z = path[-1]
        for o, tag in [(path[0], 'owner x_0'), (z, 'owner z')] + [(u, 'owner another receiver') for u in U
                                                                    if u not in path]:
            if not ok[tag] and MC.model(I, B2, o, 0, max_rest=1):
                ok[tag] = 1
        if not ok['general'] and any(MC.model(I, B2, o, 0) for o in range(E.n)):
            ok['general'] = 1
    C['  canonical chains to a receiver: (G2) fails after %s of them' % ('all' if chains and g2fail == chains else
                                                                         'none' if not g2fail else 'some')] += 1
    for tag in ['owner x_0', 'owner z', 'owner another receiver']:
        C['  M^c (max_rest 1) certifies some chain with %s: %s' % (tag, 'yes' if ok[tag] else 'no')] += 1
    any1 = ok['owner x_0'] or ok['owner z'] or ok['owner another receiver']
    C['  M^c (max_rest 1) certifies some chain' if any1 else '  M^c (max_rest 1) certifies NO chain'] += 1
    C['  M^c (any owner, any rest) certifies some chain' if ok['general'] else
      '  M^c (any owner, any rest) certifies NO chain'] += 1
    if not any1:
        out.append(('no M^c-1 certificate', dict(info, g2fail=g2fail, chains=chains)))


R.test_start = test_start

if __name__ == '__main__':
    print('$ python3 k4/ttc/r2_mc.py', *sys.argv[1:], flush=True)
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
