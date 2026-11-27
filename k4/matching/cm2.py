"""Conjecture CM2 (k4/matching.md §5): two sequential moves, the second one an exchange of Lemma EX*.

For each start: does some official first move M1 (k4/sdc/oc1_mc2_rand.Inst.moves) lead to a state B1 at which some
official chain P, improving H0 and owner o satisfy Lemma EX*'s hypothesis (exchange.ex_value_general: d <= s)?
Soundness of EX* is checked on every witness found (raw S* completion of the resulting state owned by o), and every
first-move state is checked for the plain OC2 (some second move reaches a one-absorber completion; raw).

    python3 k4/matching/cm2.py n4 | n4all | k5 | FILE.jsonl (rows of hard_starts.py)
For each start the script also reports whether CM itself (one exchange at the picks, Lemma EX*) holds."""
import sys, os, json, collections, time, multiprocessing as mp
import _mpaths  # noqa: F401
from mlib import M, INF
from exchange import ex_star_witness
from cex_deficiency import PW5, RD5


def job(item):
    name, sets, vals, Y = item
    I = M(sets, vals, None, name); base = [[g] if g is not None else [] for g in Y]; C = collections.Counter()
    first = I.moves(base); n_ex = 0; n_oc2 = 0
    cm1 = ex_star_witness(I, base) is not None
    oc1 = any(I.complete(B1, 0, 'oa') is not None for B1 in first)
    C['CM (one exchange) %s, OC1 %s' % (cm1, oc1)] += 1
    for B1 in first:
        w = ex_star_witness(I, B1)
        if w:
            P, H0, Hs, o, Bp = w
            if I.complete(Bp, 0, 'ss', [o]) is None: C['EX* VIOLATION'] += 1
            n_ex += 1
        if w or any(I.complete(B2, 0, 'oa') is not None for B2 in I.moves(B1)): n_oc2 += 1
    C['starts'] += 1
    C['CM2 holds' if n_ex else 'CM2 FAILS'] += 1
    C['OC2 holds' if n_oc2 else 'OC2 FAILS'] += 1
    return name, Y, len(first), n_ex, n_oc2, C


if __name__ == '__main__':
    src = sys.argv[1]
    if src == 'n4':
        D = json.load(open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'oc1max_cex_n4.json')))['instances']
        items = [('n4cex-%d' % t, d['sets'], d['vals'], tuple(d['picks'])) for t, d in enumerate(D)]
    elif src == 'n4all':   # every distinct maximum-matching pick vector of the 11 instances with no one-absorber completion
        import itertools
        D = json.load(open(os.path.join(_mpaths.ROOT, 'results', 'k4_matching', 'data', 'oc1max_cex_n4.json')))['instances']
        items = []
        for t, d in enumerate(D):
            I = M(d['sets'], d['vals']); N = I.nu()
            for Y in sorted(set(I.sd(o) for o in itertools.permutations(range(I.n))), key=str):
                if sum(1 for y in Y if y is not None) != N: continue
                if I.complete([[g] if g is not None else [] for g in Y], 0, 'oa') is not None: continue
                items.append(('n4cex-%d' % t, d['sets'], d['vals'], Y))
    elif src == 'k5':
        items = [('PW5', PW5[0], PW5[1], (0, 1, 2, 3, 4)), ('RD5', RD5[0], RD5[1], (1, 3, 4, 2))]
    else:
        items = [(r['name'], r['sets'], r['vals'], tuple(r['picks'])) for r in map(json.loads, open(src))]
    print('$ python3 k4/matching/cm2.py', sys.argv[1], flush=True)
    T = collections.Counter(); t0 = time.time()
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for name, Y, nf, ne, no, C in pool.imap(job, items):
            T.update(C)
            print(name, 'picks', list(Y), '| first moves', nf, '| first moves after which an EX* exchange repairs', ne,
                  '| first moves after which some second move repairs', no, flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
