"""Who absorbs at YRMH-F's outcome? (k4/sdc.md §31, RF-canon.)  For each failing start Y of d1's off-export walk dump
and each receiver u, Z = YRMH-F(Y, u first) (first listed order).  Where Z's picks complete (OC1 raw check), list
every absorber a of a one-absorber completion (a takes >= 2 junk goods, the rest go one each to distinct others;
a = None: every junk good to a distinct agent) and classify a: u itself; a pickless agent; a receiver at Z (pick
holder whose pick nobody prefers to their own); other.  Where Z needs one move, the same for the moved state.
Guides a sufficient completion condition at Z.
    python3 k4/sdc/rf_canon_absorber.py [STRIDE]"""
import os, sys, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ttc'))
from oc1_mc2_rand import Inst
import rf_diag as D

F = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'results', 'k4_rf_offexport',
                 'rf_walk_n5_stored_fails.jsonl.gz')


def absorbers(I, base):
    """All a (None or agent) that admit a one-absorber completion of base (same search as Inst.one_absorber)."""
    n = I.n; J = [g for g in range(I.m) if all(g not in b for b in base)]; out = set()
    for a in [None] + list(range(n)):
        found = False
        for r in range(0 if a is None else 2, len(J) + 1):
            if a is None and r: break
            for S in itertools.combinations(J, r):
                rest = [g for g in J if g not in S]; others = [i for i in range(n) if i != a]
                for recv in itertools.permutations(others, len(rest)):
                    B = [list(b) for b in base]
                    if a is not None: B[a] += list(S)
                    for g, i in zip(rest, recv): B[i].append(g)
                    if I.efx0(B): found = True; break
                if found: break
            if found: break
        if found: out.add(a)
    return out, len(J)


def receivers(I, base):
    n = I.n; p = [I.V(i, base[i]) for i in range(n)]
    return [u for u in range(n) if len(base[u]) == 1 and all(I.v[i].get(base[u][0], 0) <= p[i] for i in range(n) if i != u)]


def label(I, base, a, u):
    if a is None: return 'none (all junk singletons)'
    tags = []
    if a == u: tags.append('u')
    if not base[a]: tags.append('pickless')
    elif a in receivers(I, base): tags.append('receiver')
    return '+'.join(tags) if tags else 'other (wanted pick)'


def job(r):
    I = Inst(r['sets'], r['vals']); Y = tuple(r['picks'])
    o = next(o for o in itertools.permutations(range(I.n)) if I.sd(o) == Y)
    C = collections.Counter()
    for u in r['receivers']:
        Z, od = D.feasible_sd(I, Y, [u] + [a for a in o if a != u])
        if Z == ('stuck',): C['stuck'] += 1; continue
        base = [[p] if p is not None else [] for p in Z]
        A, nj = absorbers(I, base)
        if A:
            C['Z complete'] += 1
            labs = sorted(set(label(I, base, a, u) for a in A))
            for l in labs: C['Z complete: some absorber is %s' % l] += 1
            C['Z complete: u absorbs: %s' % (u in A)] += 1
            C['Z complete: u or a pickless agent or None absorbs: %s' % (u in A or None in A or any(a is not None and not base[a] for a in A))] += 1
            rz = receivers(I, base); holders = [a for a in od if base[a]]
            lastrec = max(rz, key=lambda a: od.index(a)) if rz else None
            C['Z complete: last pick holder of the realized order absorbs: %s' % (holders[-1] in A)] += 1
            C['Z complete: last pick holder is a receiver at Z: %s' % (holders[-1] in rz)] += 1
            C['Z complete: the receiver at Z latest in the realized order absorbs: %s' % (lastrec in A)] += 1
            C['Z complete: None or last receiver absorbs: %s' % (None in A or lastrec in A)] += 1
            C['Z complete: every receiver at Z absorbs: %s' % all(a in A for a in rz)] += 1
            C['Z complete: some receiver-at-Z (incl. u, pickless) absorbs: %s' % any(
                a is None or not base[a] or a in receivers(I, base) for a in A)] += 1
            continue
        C['Z needs a move'] += 1
        best = None
        for st in I.moves(base):
            st = [list(b) for b in st]; A2, _ = absorbers(I, st)
            if A2:
                labs = set(label(I, st, a, u) for a in A2)
                best = labs if best is None else best | labs
        if best is None: C['Z: OC1 FAILS'] += 1; continue
        for l in sorted(best): C['Z move: some (move, absorber) with absorber %s' % l] += 1
    return C


if __name__ == '__main__':
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('$ python3 k4/sdc/rf_canon_absorber.py', *sys.argv[1:], flush=True)
    rows = [json.loads(l) for i, l in enumerate(gzip.open(F, 'rt')) if i % S == 0]
    print('starts', len(rows), flush=True)
    T = collections.Counter()
    with mp.Pool() as pool:
        for C in pool.imap_unordered(job, rows, chunksize=16): T.update(C)
    for k in sorted(T): print(k, T[k])
