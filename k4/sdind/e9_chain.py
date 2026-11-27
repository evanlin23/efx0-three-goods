"""E9: the starts that need a chain, seen through the reverse-SD insertion (k4/sd_induct.md §4).

For each SD outcome Y with NO one-absorber completion (OC1 needs a chain), and each order pi producing Y, insert
pi_n, ..., pi_1.  Without a chain, levels are one-absorber completions of the picks with steps <= 1.  At one level k
(inserting f = pi_k) we may apply ONE improving chain (sdilib.chains, = de_free's chains) to the picks of I^k; the
chain state must have a one-absorber completion at level k, and from there the remaining insertions (new agents
with their picks, chain bases kept) must go through with steps <= 1.  Recorded:
  * for some order / the first order: success with a chain at some level;
  * the level of the chain: only at the last level (k = 1, i.e. the chain is OC1's chain on the whole instance) or
    earlier;
  * whether some successful chain starts at the newly inserted agent f (x_0 = f) and whether f is frozen;
  * the levels at which the chain-free path breaks (the first level with no continuation).

    python3 k4/sdind/e9_chain.py special|screen|suite|logs|cores:FILES:N:SEED [NMAX]"""
import sys, itertools, collections, json, time
import numpy as np
import _paths
from sdilib import Inst, sd, wanted_by, completions, delete, picks_base, chains
from e1_delete import load
from e2_paths import sub_completions


def sub_bases(I, bases, U):
    """completions of I_U (agents U; goods = their bases + junk) with the given bases (full-instance labels);
    returns (J, A) in full labels; absent agents' bases are deleted with them"""
    U = sorted(U); rest = [i for i in range(I.n) if i not in U]
    gone = [g for i in rest for g in bases[i]]
    I2, amap, gmap = delete(I, rest, gone)
    inv = {b: a for a, b in amap.items()}
    b2 = [[gmap[g] for g in bases[a]] for a in U]
    J2, A2 = completions(I2, b2, 1)
    ginv = {b: a for a, b in gmap.items()}
    J = [ginv[g] for g in J2]
    A = np.vectorize(lambda b: inv[b], otypes=[np.int64])(A2) if A2.size else A2.reshape(len(A2), len(J2))
    return J, A


def step(P, Q):
    """indices of Q reachable from some row of P with Hamming <= 1"""
    if len(P) == 0 or len(Q) == 0: return np.array([], dtype=np.int64)
    if Q.shape[1] == 0: return np.arange(len(Q))
    D = (P[:, None, :] != Q[None, :, :]).sum(axis=2) <= 1
    return np.nonzero(D.any(axis=0))[0]


def continue_from(I, bases, seq, k0, A0):
    """from completions A0 at level k0 (present = seq[:k0]) with `bases`, insert seq[k0:], steps <= 1"""
    R = A0
    for k in range(k0 + 1, len(seq) + 1):
        J, Q = sub_bases(I, bases, seq[:k])
        idx = step(R, Q)
        if len(idx) == 0: return False
        R = Q[idx]
    return True


if __name__ == '__main__':
    src = sys.argv[1]; NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    C = collections.Counter(); t0 = time.time(); shown = collections.Counter()
    print('$ python3 k4/sdind/e9_chain.py', *sys.argv[1:], flush=True)
    for name, sets, vals, m in load(src):
        if len(sets) > NMAX or len(sets) < 2: continue
        I = Inst(sets, vals, m); C['instances'] += 1
        byY = collections.defaultdict(list)
        for o in itertools.permutations(range(I.n)):
            byY[tuple(sd(I, o)[0])].append(o)
        for Y, orders in byY.items():
            Y = list(Y); cache = {}
            try:
                full = sub_completions(I, Y, range(I.n), cache)
            except ValueError:
                C['skipped'] += 1; continue
            if len(full): continue
            C['starts needing a chain'] += 1
            W = wanted_by(I, Y)
            pb = picks_base(I, Y)
            some = False; first_ok = None; levels_used = set(); x0f = False; x0f_frozen = set(); breaks = collections.Counter()
            for oi, pi in enumerate(orders):
                seq = list(pi)[::-1]
                # chain-free reachable sets
                Rs = [sub_completions(I, Y, seq[:1], cache)]
                brk = None
                for k in range(2, I.n + 1):
                    Q = sub_completions(I, Y, seq[:k], cache)
                    idx = step(Rs[-1], Q)
                    Rs.append(Q[idx] if len(idx) else Q[:0])
                    if len(idx) == 0 and brk is None: brk = k
                breaks['first break at level %s of %d' % (brk, I.n)] += 1
                okpi = False; okk = []
                for k in range(2, I.n + 1):          # chain applied when inserting seq[k-1] (fresh completion)
                    U = seq[:k]; f = seq[k - 1]; found = False
                    # chain on the picks of I_U: build the sub-instance's bases in full labels
                    sub = [pb[i] if i in U else [] for i in range(I.n)]
                    # chains among agents of U only: run on the sub-instance
                    rest = [i for i in range(I.n) if i not in U]
                    I2, amap, gmap = delete(I, rest, [Y[i] for i in rest if Y[i] is not None])
                    inv = {b: a for a, b in amap.items()}; ginv = {b: a for a, b in gmap.items()}
                    b2 = [[gmap[g] for g in pb[a]] for a in sorted(U)]
                    for nb2, path, H in chains(I2, b2):
                        nb = [list(b) for b in pb]
                        for a2, bb in enumerate(nb2): nb[inv[a2]] = [ginv[g] for g in bb]
                        J, A0 = sub_bases(I, nb, U)
                        if len(A0) == 0: continue
                        if continue_from(I, nb, seq, k, A0):
                            okpi = True; found = True; levels_used.add(k)
                            x0 = inv[path[0]]
                            if k == brk and x0 == f: x0f = True; x0f_frozen.add(bool(W[f]))
                            if k == brk: break
                    if found: okk.append(k)
                if okpi:
                    C['orders: a chain works at the break level'] += (brk in okk)
                    C['orders: chain works at some level <= break'] += any(k <= (brk or 99) for k in okk)
                    C['orders: chain works only at the last level'] += (okk == [I.n])
                    C['orders with a chain level'] += 1
                if oi == 0: first_ok = okpi
                some |= okpi
            C['some order: chain + insertion works'] += some
            C['first order: chain + insertion works'] += bool(first_ok)
            for L in levels_used: C['a successful chain level (k): %s' % ('last (whole instance)' if L == I.n else 'earlier')] += 1
            C['some chain at the break level starts at the inserted agent'] += x0f
            for fz in x0f_frozen: C['  ... and that agent is frozen: %s' % fz] += 1
            for b, c in breaks.items(): C[b] += c
            if not some and shown['x'] < 4:
                shown['x'] += 1; print('NO CHAIN INSERTION', name, json.dumps((sets, vals)), 'picks', Y, flush=True)
    for k in sorted(C): print(k, C[k])
    print('time %.0f s' % (time.time() - t0))
