"""attempts/k4-one-local-gadget.md: reduction of a lone 4-good agent z to the k = 3 theorem by local gadgets fails.
Part 1 (this main): two 3-limited gadget agents h1, h2 (each <= 3 positive goods among z's four boundary goods) replacing a lone 4-good
agent z (single-Q4 / single-P4).  H' is 3-limited, so it has an EFX0 allocation by the k = 3 theorem; Lemma M1(b)
extension semantics of reduce4.  Coverage per state is valuation-independent, so it is computed once."""
import sys, time, numpy as np
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "k4"))
import reduce4 as R4
from multiprocessing import Pool

def main(kind):
    if kind == 'Q4': cfg = R4.Config('single-Q4', {'e': ('s', 't', 'u', 'w')}, set(), {'s', 't', 'u', 'w'}); goods = ['s', 't', 'u', 'w']
    else: cfg = R4.Config('single-P4', {'e': ('s', 't', 'u', 'p')}, {'p'}, {'s', 't', 'u'}); goods = ['s', 't', 'u']
    M = R4.menu(len(goods)); M = M[(M > 0).sum(1) <= 3]
    red = R4.Reduction(cfg, 'gad2', {'h1': ('fix', dict(zip(goods, M[0]))), 'h2': ('fix', dict(zip(goods, M[0])))}, set(), source=True)
    sts = list(red.states()); print(kind, 'menu', len(M), 'states', len(sts), flush=True)
    t0 = time.time()
    with Pool(4, initializer=R4._init, initargs=(red,)) as pool:
        covs = pool.map(R4._cover, sts, chunksize=max(1, len(sts) // 64))
    P = int(np.prod(cfg.shape))
    U = np.array([~np.unpackbits(c)[:P].astype(bool) for c in covs], dtype=np.float32)   # states x profiles: uncovered
    A1 = np.array([R4.menu_admissible(goods, M, *st, 'h1') for st in sts], dtype=np.float32)
    A2 = np.array([R4.menu_admissible(goods, M, *st, 'h2') for st in sts], dtype=np.float32)
    print('coverage and admissibility [%.0f s]; states with an uncovered profile: %d' % (time.time() - t0, int((U.sum(1) > 0).sum())), flush=True)
    keep = U.sum(1) > 0
    U, A1, A2 = U[keep], A1[keep], A2[keep]
    bad = np.zeros((len(M), len(M), P), dtype=bool)
    for p in range(P):
        if U[:, p].any(): bad[:, :, p] = (A1.T * U[:, p]) @ A2 > 0.5
    ok = ~bad                                   # [k1, k2, p]: pair (k1, k2) reduces profile p
    union = ok.any((0, 1))
    print('%s: two 3-limited gadgets reduce %d of %d types [%.0f s]' % (kind, union.sum(), P, time.time() - t0), flush=True)
    best = np.unravel_index(ok.sum(2).argmax(), ok.shape[:2])
    print('  best pair reduces', ok[best].sum(), 'h1 =', dict(zip(goods, M[best[0]].tolist())), 'h2 =', dict(zip(goods, M[best[1]].tolist())))
    left = [cfg.dom['e'][k] for k in np.nonzero(~union)[0]]
    print('  unreduced types (first 10):', left[:10], 'count', len(left))

def singles():
    """Part 2: deleting z (DEL), and every single 3-limited gadget agent on z's boundary goods."""
    for kind, S, I in (('Q4', {'e': ('s', 't', 'u', 'w')}, set()), ('P4', {'e': ('s', 't', 'u', 'p')}, {'p'})):
        cfg = R4.Config('single-' + kind, S, I, set(S['e']) - I); goods = sorted(cfg.D)
        ok, _ = R4.run(R4.Reduction(cfg, 'DEL', {}, set(), source=True), 4)
        M = R4.menu(len(goods)); M = M[(M > 0).sum(1) <= 3]
        g = R4.gadget_search(cfg, 'h', goods, set(), M, 4).any(0)
        print('%s: DEL reduces %d of %d types; one 3-limited gadget (%d menu valuations) reduces %d' % (kind, ok.sum(), ok.size, len(M), g.sum()))


if __name__ == '__main__':
    print('$ python3 attempts/k4_one_local_gadget.py', *sys.argv[1:], flush=True)
    singles()
    for kind in ('Q4', 'P4'): main(kind)
