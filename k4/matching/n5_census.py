"""Census of the second move at starts with no one-move repair (k4/matching.md §6; evidence unless the input is a
complete export).  For every input start (sets, vals, picks), with this note's code and raw EFX0:
  - hard: every agent picks, no one-absorber completion at the picks, none after any official move (OC1 fails);
  - holders: the number of holders at the picks;
  - LIFT-SHAPE+ (n4_exhaustive.lift_shape_plus; refuted at n = 5, attempts/k4-matching-lift-shape.md);
  - CM2: some official first move, then a Lemma EX* exchange (exchange.ex_star_witness);
  - OC2 and the shapes of the repairing pairs (P1 official from a dangerous agent, P2 official at B1, then a
    one-absorber completion): some pair is vertex-disjoint; some pair has P2 ending at the holder z;
  - EX* exact on the second move (every EXACT_STRIDE-th start; 1 = all);
  - OC2-REC (proof/k4-oc1max-multi, k4/oc1max_multi.md §8, Lemma LIFT + Sub-lemma OC2-REC; this is an independent
    implementation).  Some canonical chain P1 from a dangerous agent k, with an improving set T, #T = 2,
    T inside J + B_{end}, improving for a second agent dangerous at the picks, satisfies:
      (LIFT-hyp) every other agent values each good of T below its value at B1;
      (a) the reduced state B1- (k and T deleted) is a perfect SD outcome of the reduced instance I-;
      (b) B1- has a one-absorber completion in I-, at once or after one official move of I-, that lifts.  Lifting means
          k keeps T, receives nothing, and the allocation is raw EFX0 in I.
    The completion search in I- is a brute force over every owner and every one-absorber assignment of the junk, so
    "some completion that does not threaten k" is decided exactly.  Where OC2-REC holds, also whether (b) is given by
    a Lemma EX* exchange in I- (rec_ex): a Hall-type condition at the reduced state.

Input: JSONL (or .jsonl.gz) rows with sets, vals, picks; or the n = 4 export (results/k4_matching/data/
two_move_starts_n4.json.gz) with `n4export[:STRIDE]`; or `cex5` for the n = 5 counterexample of
attempts/k4-matching-lift-shape.md.

    python3 k4/matching/n5_census.py INPUT [INPUT ...]"""
import sys, os, gzip, json, itertools, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M
from lift_shapes import chain_moves
from exchange import ex_star_witness, ex_value_general
from n4_exhaustive import lift_shape_plus

EXACT_STRIDE = int(os.environ.get('EXACT_STRIDE', '1'))


def reduced(I, k, T):
    """I- without agent k and the goods T, goods renumbered; returns (I-, agent map, good map old->new, new->old)."""
    keep = [i for i in range(I.n) if i != k]
    goods = [g for g in range(I.m) if g not in T]
    g2 = {g: t for t, g in enumerate(goods)}
    sets = [[g2[g] for g in I.sets[i] if g not in T] for i in keep]
    vals = [[I.v[i][g] for g in I.sets[i] if g not in T] for i in keep]
    return M(sets, vals, m=len(goods)), keep, g2, goods


def lift_complete(I, B, k):
    """A one-absorber completion of B in I with an owner o != k in which k receives nothing (brute force), or None."""
    J = I.junk(B)
    for o in range(I.n):
        if o == k: continue
        recv = [u for u in range(I.n) if u not in (o, k)]
        for lab in itertools.product([o] + recv, repeat=len(J)):
            if any(lab.count(u) > 1 for u in recv): continue
            X = [list(b) for b in B]
            for g, u in zip(J, lab): X[u].append(g)
            if I.efx0(X): return o, X
    return None


def oc2_rec(I, base):
    """OC2-REC with the first chain's data, or None."""
    J = I.junk(base); D = I.dangerous(base)
    for P1, H01, Hs1, B1 in chain_moves(I, base, D):
        k = P1[0]; T = set(H01)
        if len(T) != 2 or any(Hs1.get(i) for i in range(1, len(P1))): continue
        if not T <= set(J) | set(base[P1[-1]]): continue
        if not any(q != k and I.V(q, [g for g in T if g in I.R[q]]) > I.V(q, base[q]) for q in D): continue
        if any(I.v[i].get(g, 0) >= I.V(i, B1[i]) for i in range(I.n) if i != k for g in T if g in I.R[i]): continue
        Im, keep, g2, goods = reduced(I, k, T)
        Bm = [[g2[g] for g in B1[i]] for i in keep]
        if any(len(b) != 1 for b in Bm): continue
        Ym = tuple(b[0] for b in Bm)
        orders = [o for o in itertools.permutations(range(Im.n)) if Im.sd(o) == Ym]
        if not orders: continue
        cands = [Bm] + Im.moves(Bm)
        for t, C in enumerate(cands):
            Cb = [None] * I.n; Cb[k] = sorted(T)
            for a, i in enumerate(keep): Cb[i] = [goods[g] for g in C[a]]
            r = lift_complete(I, Cb, k)
            if r is not None:
                return {'P1': P1, 'T': sorted(T), 'moves in I-': t > 0, 'owner': r[0], 'alloc': r[1],
                        'P1 ends at the holder': P1[-1] in I.holders(base), 'B1': B1, 'B2': Cb,
                        'reduced order': [keep[a] for a in orders[0]]}
    return None


def rec_ex(I, base):
    """OC2-REC with (b) given by a Lemma EX* exchange in I- (a static Hall-type condition at the reduced state): some
    first chain as in oc2_rec with (LIFT-hyp) and (a), some chain of I- at B1- and owner o satisfying EX* there, and
    the resulting state of I- lifts to a completion of I (k keeps T and receives nothing).  Returns bool."""
    J = I.junk(base); D = I.dangerous(base)
    for P1, H01, Hs1, B1 in chain_moves(I, base, D):
        k = P1[0]; T = set(H01)
        if len(T) != 2 or any(Hs1.get(i) for i in range(1, len(P1))): continue
        if not T <= set(J) | set(base[P1[-1]]): continue
        if not any(q != k and I.V(q, [g for g in T if g in I.R[q]]) > I.V(q, base[q]) for q in D): continue
        if any(I.v[i].get(g, 0) >= I.V(i, B1[i]) for i in range(I.n) if i != k for g in T if g in I.R[i]): continue
        Im, keep, g2, goods = reduced(I, k, T)
        Bm = [[g2[g] for g in B1[i]] for i in keep]
        if any(len(b) != 1 for b in Bm): continue
        if not any(Im.sd(o) == tuple(b[0] for b in Bm) for o in itertools.permutations(range(Im.n))): continue
        for P, H0, Hs, B2m in chain_moves(Im, Bm):
            if not any(ex_value_general(Im, Bm, P, B2m, o)[0] <= 0 for o in range(Im.n)): continue
            Cb = [None] * I.n; Cb[k] = sorted(T)
            for a, i in enumerate(keep): Cb[i] = [goods[g] for g in B2m[a]]
            if lift_complete(I, Cb, k) is not None: return True
    return False


def job(row):
    sets, vals, picks = row['sets'], row['vals'], row['picks']
    I = M(sets, vals); base = [[g] for g in picks]; C = collections.Counter(); z = None
    first = I.moves(base) if all(y is not None for y in picks) else []
    hard = bool(first) and I.complete(base, 0, 'oa') is None and all(I.complete(B1, 0, 'oa') is None for B1 in first)
    C['hard, OC1 fails (raw) %s' % hard] += 1
    if not hard: return C, None
    hold = I.holders(base); C['holders = %d' % len(hold)] += 1
    if len(hold) == 1: z = hold[0]
    C['LIFT-SHAPE+ %s' % (lift_shape_plus(I, base) is not None)] += 1
    cm2 = any(ex_star_witness(I, B1) is not None for B1 in first)
    C['CM2 %s' % cm2] += 1
    D = I.dangerous(base); disj = toz = oc2 = False
    for P1, H01, Hs1, B1 in chain_moves(I, base, D):
        for P2, H02, Hs2, B2 in chain_moves(I, B1, I.dangerous(B1)):
            if (disj or set(P1) & set(P2)) and (toz or P2[-1] != z): continue
            if I.complete(B2, 0, 'oa') is not None:
                oc2 = True; disj |= not set(P1) & set(P2); toz |= P2[-1] == z
        if disj and toz: break
    C['OC2 (chains from dangerous agents) %s' % oc2] += 1
    C['  a repairing pair is vertex-disjoint %s' % disj] += 1
    C['  a repairing pair has P2 ending at the holder %s' % toz] += 1
    if row.get('_k', 0) % EXACT_STRIDE == 0:
        ex1 = [ex_star_witness(I, B1) is not None for B1 in first]
        oc2m = [e or any(I.complete(B2, 0, 'oa') is not None for B2 in I.moves(B1)) for e, B1 in zip(ex1, first)]
        C['(EX* sample) exact on the second move %s' % (ex1 == oc2m)] += 1
    rec = oc2_rec(I, base)
    C['OC2-REC %s' % (rec is not None)] += 1
    if rec is not None:
        C['  OC2-REC: B1- completes at once %s' % (not rec['moves in I-'])] += 1
        C['  OC2-REC: P1 ends at the holder %s' % rec['P1 ends at the holder']] += 1
        C['  OC2-REC with (b) by a Lemma EX* exchange in I- %s' % rec_ex(I, base)] += 1
        assert I.efx0(rec['alloc'])
        rec = {'k': row.get('_k'), 'P1': rec['P1'], 'T': rec['T'], 'B1': rec['B1'], 'reduced order': rec['reduced order'],
               'B2': rec['B2'], 'owner': rec['owner'], 'alloc': rec['alloc']}
    else:
        print('OC2-REC FAILS', json.dumps({'sets': sets, 'vals': vals, 'picks': list(picks)}), flush=True)
    if not cm2: print('CM2 FAILS', json.dumps({'sets': sets, 'vals': vals, 'picks': list(picks)}), flush=True)
    return C, rec


def load(arg):
    if arg == 'cex5':
        return [dict(sets=[[0, 2, 3, 7], [1, 2, 6, 7], [3, 4, 5, 6], [3, 4, 5, 7], [4, 5, 6, 7]],
                     vals=[[1, 8, 6, 4], [4, 8, 2, 7], [6, 7, 3, 5], [7, 10, 2, 6], [7, 5, 3, 6]], picks=[7, 2, 3, 5, 4],
                     orders=[[1, 4, 2, 0, 3]])]
    if arg.startswith('n4export'):
        st = int(arg.split(':')[1]) if ':' in arg else 1
        d = json.load(gzip.open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'two_move_starts_n4.json.gz'), 'rt'))
        rows = [dict(sets=hg['sets'], vals=s['vals'], picks=s['picks'], orders=s.get('orders'))
                for hg in d['hypergraphs'] for s in hg['starts']]
        return rows[::st]
    op = gzip.open if arg.endswith('.gz') else open
    return [json.loads(l) for l in op(arg, 'rt') if l.strip()]


if __name__ == '__main__':
    rows = []
    for a in sys.argv[1:]: rows += load(a)
    seen = set(); R = []
    for r in rows:
        key = json.dumps([r['sets'], r['vals'], list(r['picks'])])
        if key not in seen: seen.add(key); R.append(dict(sets=r['sets'], vals=r['vals'], picks=list(r['picks'])))
    for t, r in enumerate(R): r['_k'] = t
    print('$ python3 k4/matching/n5_census.py', *sys.argv[1:], '|', len(R), 'distinct starts (EXACT_STRIDE=%d)' % EXACT_STRIDE, flush=True)
    T = collections.Counter(); t0 = time.time(); WIT = []
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for t, (C, rec) in enumerate(pool.imap_unordered(job, R, chunksize=4 if len(R) > 1000 else 1)):
            T.update(C)
            if rec is not None: WIT.append(rec)
            if (t + 1) % 10000 == 0: print('...', t + 1, '%.0f s' % (time.time() - t0), flush=True)
    for k in sorted(T): print(k, T[k])
    if os.environ.get('REC_WIT'):   # OC2-REC witnesses, indexed by k = position in the distinct input rows
        WIT.sort(key=lambda w: w['k'])
        with gzip.open(os.environ['REC_WIT'], 'wt') as f:
            json.dump({'what': 'OC2-REC witnesses (k4/matching/n5_census.py): per start k (index into the distinct input rows, '
                               'in input order), the first chain P1 from k = P1[0] with T, the state B1 after it, an SD order '
                               'of the reduced instance giving B1 minus k and T, the state B2 (= B1, or after one official '
                               'move of the reduced instance; k keeps T), the owner and the final allocation',
                       'inputs': sys.argv[1:], 'witnesses': WIT}, f)
        print('wrote', os.environ['REC_WIT'], len(WIT), 'witnesses')
    print('time %.0f s' % (time.time() - t0))
