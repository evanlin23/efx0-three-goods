"""Repairing moves at YRMH-F's outcome (k4/sdc.md §31, RF-canon): for each failing start Y of d1's off-export walk dump
and each receiver u, where Z = YRMH-F(Y, u first) has no one-absorber completion, list the official moves (raw
generator oc1_mc2_rand.Inst.moves) after which one exists, by type: a grab (one agent takes junk) or a chain / ring,
with the status at Z of each agent it changes (receiver, pickless, frozen-safe, dangerous, D_T); t(Z) = number of
truly dangerous agents at Z.
    python3 k4/sdc/rf_canon_movetype.py [STRIDE]"""
import sys, os, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ttc'))
from oc1_mc2_rand import Inst
import rf_diag as D
from rf_canon_absorber import absorbers, receivers, F
from rf_canon_bycase import tcount

def status(I, base, x):
    n=I.n; J=[g for g in range(I.m) if all(g not in b for b in base)]
    p=[I.V(i, base[i]) for i in range(n)]
    if not base[x]: return 'pickless'
    fro = any(i!=x and I.V(i, base[x]) > p[i] for i in range(n))
    if not fro: return 'receiver'
    vj = I.V(x, J)
    return 'D_T' if vj > p[x] else ('dangerous' if vj > 0 else 'frozen-safe')

def job(r):
    I = Inst(r['sets'], r['vals']); Y = tuple(r['picks'])
    o = next(o for o in itertools.permutations(range(I.n)) if I.sd(o) == Y)
    C = collections.Counter()
    for u in r['receivers']:
        Z, od = D.feasible_sd(I, Y, [u] + [a for a in o if a != u])
        if Z == ('stuck',): continue
        base = [[p] if p is not None else [] for p in Z]
        A, nj = absorbers(I, base)
        if A: continue
        C['needs move'] += 1
        C['  t(Z)=%d' % tcount(I, Z)] += 1
        types = set()
        for st in I.moves(base):
            st = [list(b) for b in st]; A2, _ = absorbers(I, st)
            if not A2: continue
            ch = [i for i in range(I.n) if sorted(st[i]) != sorted(base[i])]
            if len(ch) == 1:
                x = ch[0]; typ = 'grab by %s' % status(I, base, x)
            else:
                lost = [i for i in ch if base[i] and base[i][0] not in st[i]]
                typ = 'chain/ring of %d (%s)' % (len(ch), ','.join(sorted(status(I, base, i) for i in ch)))
            types.add(typ)
        for t in types: C['  repairing move: ' + t] += 1
        C['  some grab repairs: %s' % any(t.startswith('grab') for t in types)] += 1
        C['  some grab by D_T repairs: %s' % any(t == 'grab by D_T' for t in types)] += 1
    return C

if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/sdc/rf_canon_movetype.py', *sys.argv[1:], flush=True)
    rows = [json.loads(l) for i, l in enumerate(gzip.open(F, 'rt')) if i % S == 0]
    T = collections.Counter()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, rows, chunksize=16): T.update(C)
    for k in sorted(T): print(k, T[k])
