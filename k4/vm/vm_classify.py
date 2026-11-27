"""Classify instances by the simplest repair VM1 needs (coordinator's request, k4/vm.md section 7.5).  Over every
V-M matching Y (Phases I-II), the simplest class reached by some Y:
  HDT        one unfrozen owner, the frozen agents' danger goods in distinct unfrozen slots (Proposition HDT)
  absorbers  Y extends to an EFX0 allocation in which every agent frozen at Y stays a single good, but not HDT
             (several agents receive two or more goods)
  unfreezing Y extends, but in every extension some agent frozen at Y receives goods (its wanters have risen)
  rotation   Y extends to no EFX0 allocation, yet F1 placements with envy-cycle rotation complete it
  one move   none of the above at any V-M matching; one VMx move (unrestricted exchanges), then F1 + rotation
  NONE       none of the above (would refute VM1)
SAT checks use k4/sdc/sdclib.Enc (exact EFX0).  EVIDENCE only.
    python3 k4/vm/vm_classify.py SOURCE"""
import sys, os, collections, json, time, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
from vm_test import items_for
from vm_extend import Enc
from vm_hall import analyse
from vm_max import no_move_runs
import vmx2_phases as P
from pysat.solvers import Cadical153

ORDER = ['HDT', 'absorbers', 'unfreezing', 'rotation', 'one move', 'NONE']


def extends(E, Y, frozen_single):
    cl = list(E.cl)
    for g in range(E.m):
        cl.append([-E.x[g][E.n]])
    for i, B in enumerate(Y):
        for g in B:
            cl.append([E.x[g][i]])
        if i in frozen_single:
            for g in range(E.m):
                if g not in B:
                    cl.append([-E.x[g][i]])
    S = Cadical153(bootstrap_with=cl); ok = S.solve(); S.delete(); return ok


def classify(I, E):
    best = 5; m = I.m
    Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            Y = [list(b) for b in r[0]]
            if Y not in Ys: Ys.append(Y)
    for Y in Ys:
        own = [I.val(i, Y[i]) for i in range(I.n)]
        frozen = set(j for j in range(I.n) if Y[j] and any(i != j and I.val(i, Y[j]) > own[i] for i in range(I.n)))
        if analyse(I, Y)['hdt']: return 0
        if extends(E, Y, frozen): best = min(best, 1); continue
        if extends(E, Y, set()): best = min(best, 2); continue
        if best > 3 and no_move_runs(I, Y, 20000)[0]: best = min(best, 3)
    if best <= 3: return best
    V.FREE_Z[0] = True
    for Y in Ys:
        pool = set(range(m)) - set(g for b in Y for g in b)
        Z0 = [list(b) for b in Y]; V.l3_source(I, Z0)
        for mv in V.exchanges(I, Z0, pool):
            Z, Pz = P.apply_move(Z0, pool, mv)
            W = [list(b) for b in Z]; V.l3_source(I, W)
            if P.phase_b(I, W, Pz, 20000)[0]:
                return 4
    return 5


def one(args):
    name, sets, vals, m = args
    I = V.Inst(sets, vals, m); E = Enc(sets, vals, m)
    return name, I.n, I.m, max(map(len, sets)), classify(I, E)


if __name__ == '__main__':
    src = sys.argv[1]
    print('$ python3 k4/vm/vm_classify.py', ' '.join(sys.argv[1:]))
    C = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
    with mp.Pool(os.cpu_count()) as pool:
        for name, n, m, k, c in pool.imap_unordered(one, items_for(src), chunksize=4):
            C[ORDER[c]] += 1; ex[ORDER[c]].append((n, m, name))
    for c in ORDER:
        print('%-12s %d   %s' % (c, C[c], ', '.join('%s(n=%d,m=%d)' % (nm, n, m) for n, m, nm in sorted(ex[c])[:6])))
    print('time %.0f s' % (time.time() - t0))
