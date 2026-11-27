"""REC-LOW's rank-2 one-move starts (k4/sdc.md §31, K4.SDC.RECLOW): over the complete n = 4 failure export, at every
maximum-matching SD vector Y whose best receiver holds rank 2 and whose picks do not complete, list the official moves
(raw generator oc1_mc2_rand.Inst.moves) after which a one-absorber completion exists.  For each rank-2 receiver u with
top good x = Y_w (held by w): does a repairing move give u the good x?  Is it the plain swap (u takes Y_w, w takes Y_u,
possibly with junk)?  Which agents move, and with what status at Y (receiver, frozen-safe, dangerous, D_T)?
    python3 k4/sdc/rec_low_rank2_moves.py [STRIDE]"""
import sys, os, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst
from oc1_max_orders import nu
from extremal_rank_check import ranks
from rec_low_rand import recs
from rf_canon_absorber import absorbers
from rf_canon_movetype import status


def job(a):
    sets, vals = a; I = Inst(sets, vals); n = I.n; N = nu(I); C = collections.Counter(); ex = None
    for Y in set(I.sd(o) for o in itertools.permutations(range(n))):
        if sum(x is not None for x in Y) != N: continue
        rz = recs(I, Y); rk = ranks(I, Y)
        if not rz or min(rk[u] for u in rz) != 2: continue
        base = [[p] if p is not None else [] for p in Y]
        if absorbers(I, base)[0]: continue
        C['rank-2 vectors needing a move'] += 1
        U = [u for u in rz if rk[u] == 2]
        top = {u: max(I.R[u], key=lambda g: I.v[u][g]) for u in U}
        own = {Y[i]: i for i in range(n) if Y[i] is not None}
        rep = []
        for st in I.moves(base):
            st = [list(b) for b in st]
            if absorbers(I, st)[0]: rep.append(st)
        if not rep: C['  OC1 FAILS (REC-LOW counterexample)'] += 1; ex = (sets, vals, Y); continue
        kinds = set(); utop = False; swap = False
        for st in rep:
            ch = [i for i in range(n) if sorted(st[i]) != sorted(base[i])]
            kinds.add('%d agents (%s)' % (len(ch), ','.join(sorted(('u' if i in U else status(I, base, i)) for i in ch))))
            for u in U:
                w = own[top[u]]
                if top[u] in st[u]:
                    utop = True
                    if Y[u] in st[w] and set(ch) == {u, w}: swap = True
        for k in kinds: C['  repairing move: ' + k] += 1
        C['  some repairing move gives a rank-2 receiver its top good: %s' % utop] += 1
        C['  some repairing move is the swap of u with the holder of its top good: %s' % swap] += 1
        C['  repairing moves involve u: %s' % any(any(sorted(st[u]) != sorted(base[u]) for u in U) for st in rep)] += 1
        if not utop and ex is None: ex = ('no u-top move', sets, vals, Y)
    return C, ex


if __name__ == '__main__':
    print('$ python3 k4/sdc/rec_low_rank2_moves.py', *sys.argv[1:], flush=True)
    d = json.load(gzip.open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_oc1max',
                                         'two_move_starts_n4.json.gz')))
    prof = {}
    for h in d['hypergraphs']:
        for st in h['starts']: prof[(json.dumps(h['sets']), json.dumps(st['vals']))] = (h['sets'], st['vals'])
    tasks = list(prof.values())[::int(sys.argv[1]) if len(sys.argv) > 1 else 1]
    print('profiles', len(tasks), flush=True)
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks, chunksize=16):
            T.update(C)
            if ex and shown < 2: shown += 1; print('EXAMPLE', json.dumps(ex), flush=True)
    for k in sorted(T): print(k, T[k])
