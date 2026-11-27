"""Uncapped verification of a VM1 failure (k4/vm.md section 7.7): for an instance given as JSON {sets, vals, m}, list
every V-M matching; for depth d = 0, 1, 2, ... (moves: pool upgrades and unrestricted two-agent exchanges, as in
vm6x_run), the set of states reachable with at most d moves (rotations applied in between); from each, an exhaustive
memoized search over F1 placements with rotation.  Prints the least d with a completion (or none up to --maxd), and
whether an EFX0 allocation exists at all (SAT, sdclib.Enc).  EVIDENCE only (single implementation; see the
attempts file for an independent replay).
    python3 k4/vm/vm1_verify.py JSON [--maxd=2]"""
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmlib as V
import vmx2_phases as P
from vm_extend import Enc, completable


def key(X):
    return tuple(tuple(sorted(b)) for b in X)


def placeable(I, X0, pool0):
    stack = [([list(b) for b in X0], frozenset(pool0))]; seen = set(); n_states = 0
    while stack:
        X, pool = stack.pop(); V.l3_source(I, X)
        k = key(X)
        if k in seen: continue
        seen.add(k); n_states += 1
        valued = [g for g in pool if I.valued_by(g)]
        if not valued:
            return X, n_states
        for g in valued:
            for s in range(I.n):
                if V.safe_add(I, X, s, g):
                    Y = [list(b) for b in X]; Y[s].append(g); stack.append((Y, pool - {g}))
    return None, n_states


if __name__ == '__main__':
    d = json.loads(sys.argv[1]); opt = dict(a[2:].split('=') for a in sys.argv[2:] if a.startswith('--'))
    maxd = int(opt.get('maxd', 2)); V.FREE_Z[0] = True
    I = V.Inst(d['sets'], d['vals'], d['m']); E = Enc(d['sets'], d['vals'], d['m'])
    print('EFX0 allocation exists:', completable(E, [[] for _ in range(I.n)]))
    Ys = []
    for ch, r in V.all_runs(V.vm_run, I, stop='II'):
        if not isinstance(r, V.Stuck):
            Y = [list(b) for b in r[0]]
            if Y not in Ys: Ys.append(Y)
    print('V-M matchings:', Ys)
    frontier = []
    for Y in Ys:
        Z = [list(b) for b in Y]; V.l3_source(I, Z); frontier.append((Z, set(range(I.m)) - set(g for b in Y for g in b)))
    seen = set(key(Z) for Z, _ in frontier); t0 = time.time(); total = 0
    for depth in range(maxd + 1):
        for Z, Pz in frontier:
            X, ns = placeable(I, Z, Pz); total += ns
            if X is not None:
                assert V.is_efx0(I, X)
                print('completion with %d move(s): %s  (placement states searched %d, %.0fs)' % (depth, X, total, time.time() - t0))
                sys.exit(0)
        print('depth %d: %d states, none placeable (placement states searched %d, %.0fs)' % (depth, len(frontier), total, time.time() - t0), flush=True)
        nxt = []
        for Z, Pz in frontier:
            for mv in V.exchanges(I, Z, Pz):
                W, Pw = P.apply_move(Z, Pz, mv); V.l3_source(I, W)
                if key(W) not in seen:
                    seen.add(key(W)); nxt.append((W, Pw))
        frontier = nxt
        if not frontier:
            print('no further moves'); break
    print('NO completion with at most %d moves' % maxd)
