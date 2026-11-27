"""LIFT-SHAPE+ and CM2 on EVERY n = 4 start with no one-move repair (k4/matching.md §6).

Data: results/k4_matching/data/two_move_starts_n4.json.gz, a copy of results/k4_oc1max/two_move_starts_n4.json.gz on
compute/k4-oc1max-cert (PR #114).  These are all 112,880 OC1^max failures at n = 4, over every strict profile of the
11 failing core hypergraphs; completeness is that session's certificate (its ordinal CEGAR, checked there by
check_two_move_starts_n4.log), not this script's.  Values are integer representatives of the order types, so the
statements tested here (which depend only on comparisons of disjoint sets) are decided for every strict profile.

For every start, with this note's own code:
  - hard: no one-absorber completion at the picks (raw); every agent picks; exactly one holder;
  - LIFT-SHAPE+: some LIFT-red pair meets (L3) and either case (a) of Lemma LIFT-1 [(L1), (L2')] or case (b)
    [z values the owner's bundle X = H0 of P2 + all junk at most v_z(t)], and Lemma LIFT-1's allocation is EFX0 (raw);
  - CM2: some official first move leads to a state with a Lemma EX* exchange (exchange.ex_star_witness), and the
    exchange's state has a raw S* completion owned by its owner;
  - with EXACT=1 (default: every 20th start), also whether EX* is exact on the second move.

    python3 k4/matching/n4_exhaustive.py [STRIDE]"""
import sys, os, gzip, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from lift_shapes import chain_moves
from exchange import ex_star_witness

EXACT_STRIDE = int(os.environ.get('EXACT_STRIDE', '20'))
WIT = [] if os.environ.get('WITNESSES', '1') == '1' else None   # write results/k4_matching/lift_n4_witnesses.json.gz


def lift_shape_plus(I, base, diag=None):
    """Some LIFT-red pair meeting (L3) and either case (a) [(L1) and (L2')] or case (b) [z values X at most v_z(t)];
    returns (allocation of Lemma LIFT-1, description) or None.  diag (a Counter) records the conditions' outcomes."""
    Y = [b[0] for b in base]; J = I.junk(base); D = I.dangerous(base); hold = I.holders(base)
    if len(hold) != 1: return None
    z = hold[0]; best = None
    for P1, H01, Hs1, B1 in chain_moves(I, base, D):
        if P1[-1] != z or len(H01) != 2 or not set(H01) <= set(J) | {Y[z]} or z in I.frozen(B1): continue
        if any(Hs1.get(i) for i in range(1, len(P1))): continue
        if not any(q != P1[0] and I.V(q, [g for g in H01 if g in I.R[q]]) > I.V(q, base[q]) for q in D): continue
        for P2, H02, Hs2, B2 in chain_moves(I, B1):
            h = P2[0]
            if P2[-1] != z or h == P1[0] or any(Hs2.get(i) for i in range(1, len(P2))) or len(B2[z]) != 1: continue
            t = B2[z][0]
            if I.v[z][t] < max(I.v[z].values()): continue
            J2 = I.junk(B2); X = list(B2[h]) + J2
            G = [g for g in J2 if g in I.R[z]]; gb = max([I.v[z][g] for g in G] + [0])
            L1 = z not in I.frozen(B2)
            L2p = I.V(z, [g for g in B2[h] if g in I.R[z]]) <= I.v[z][t] + gb
            L3 = all(len(set(X) & I.R[i]) <= 1 for i in range(I.n) if i not in (h, z))
            Zb = I.V(z, [g for g in X if g in I.R[z]]) <= I.v[z][t]
            if diag is not None:
                diag['L1 %s, L2p %s, L3 %s, case-b %s' % (L1, L2p, L3, Zb)] += 1
            if not L3: continue
            if L1 and L2p:
                A = [list(b) for b in B2]
                if G:
                    g = max(G, key=lambda x: I.v[z][x]); A[h] = [x for x in X if x != g]; A[z] = [t, g]
                else:
                    A[h] = X
                return A, (P1, H01, P2, H02, h, 'case a')
            if Zb:
                A = [list(b) for b in B2]; A[h] = X
                best = best or (A, (P1, H01, P2, H02, h, 'case b'))
    return best


def job(args):
    sets, vals, picks, k = args
    I = M(sets, vals); base = [[g] for g in picks]; C = collections.Counter()
    hard = all(y is not None for y in picks) and I.complete(base, 0, 'oa') is None
    C['hard perfect start (raw) %s' % hard] += 1
    C['holders = %d' % len(I.holders(base))] += 1
    r = lift_shape_plus(I, base)
    C['LIFT-SHAPE+ holds %s' % (r is not None)] += 1
    if r is not None: C['LIFT-SHAPE+ via %s' % r[1][-1]] += 1
    if r is not None:
        A = r[0]; ok = I.efx0(A) and sorted(x for b in A for x in b) == list(range(I.m))
        P1, H01, P2, H02, h, case = r[1]
        C['__witness__'] = json.dumps({'k': k, 'P1': P1, 'H01': list(H01), 'P2': P2, 'H02': list(H02), 'owner': h,
                                       'case': case[-1], 'alloc': A})
        C['LIFT-1 allocation raw EFX0 %s' % ok] += 1
        if not ok: print('LIFT-1 FAILS', json.dumps([sets, vals, picks]), r[1], flush=True)
    else:
        dg = collections.Counter(); lift_shape_plus(I, base, dg)
        for kk in dg: C['  (no qualifying pair) some pair has: ' + kk] += 1
        print('LIFT-SHAPE+ FAILS', json.dumps([sets, vals, picks]), dict(dg), flush=True)
    first = I.moves(base); ex = None
    for B1 in first:
        w = ex_star_witness(I, B1)
        if w:
            ex = w; break
    C['CM2 holds %s' % (ex is not None)] += 1
    if ex is not None:
        P, H0, Hs, o, B2 = ex
        C['CM2 witness has a raw S* completion %s' % (I.complete(B2, 0, 'ss', [o]) is not None)] += 1
    else:
        print('CM2 FAILS', json.dumps([sets, vals, picks]), flush=True)
    if k % EXACT_STRIDE == 0:
        ex1 = [ex_star_witness(I, B1) is not None for B1 in first]
        oc2 = [e or any(I.complete(B2, 0, 'oa') is not None for B2 in I.moves(B1)) for e, B1 in zip(ex1, first)]
        C['(sample) EX* exact on the second move %s' % (ex1 == oc2)] += 1
        if ex1 != oc2: print('EX* INEXACT', json.dumps([sets, vals, picks]), sum(ex1), sum(oc2), flush=True)
    return C


if __name__ == '__main__':
    STRIDE = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    d = json.load(gzip.open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'two_move_starts_n4.json.gz'), 'rt'))
    tasks = []
    for hg in d['hypergraphs']:
        for s in hg['starts']: tasks.append((hg['sets'], s['vals'], s['picks'], len(tasks)))
    tasks = tasks[::STRIDE]
    print('$ python3 k4/matching/n4_exhaustive.py', *sys.argv[1:], '|', len(tasks), 'starts (EXACT_STRIDE=%d)' % EXACT_STRIDE, flush=True)
    T = collections.Counter(); t0 = time.time(); done = 0
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for C in pool.imap_unordered(job, tasks, chunksize=16):
            w = C.pop('__witness__', None)
            if w is not None and WIT is not None: WIT.append(json.loads(w))
            T.update(C); done += 1
            if done % 10000 == 0: print('...', done, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    if WIT is not None:
        WIT.sort(key=lambda w: w['k'])
        out = os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'lift_n4_witnesses.json.gz')
        with gzip.open(out, 'wt') as f:
            json.dump({'what': 'for every n = 4 start with no one-move repair (two_move_starts_n4.json.gz, in its order; k is the '
                               'index), a LIFT-SHAPE+ witness: first chain P1 with H01, second chain P2 with H02, owner, '
                               'Lemma LIFT-1 case, and the final allocation', 'witnesses': WIT}, f)
        print('wrote', os.path.relpath(out, _mpaths.ROOT), len(WIT), 'witnesses')
    print('time %.0f s' % (time.time() - t0))
