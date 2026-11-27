"""Census of the R2-C repairs at the hard starts where (S) fails (TTC's request, k4/ttc.md §14.6; workstream
compute/k4-oc1max-cert).

The starts: perfect SD starts with at least two receivers, no one-absorber completion of the picks, and no (S) repair.
(S) is a canonical chain with no junk past its head, then a one-absorber completion.
- They are enumerated exactly: cegar.Cert(r2='s') is run to UNSAT with every failing (profile, picks) pair blocked one
  by one.
- At each start, the repairing canonical chains (R2-C, any one-absorber completion) are listed by the raw code of
  verify_r2.py, and each chain gets a shape:
  - which positions take junk: 'end' (H_t), 'mid-receiver', 'mid-dangerous' (frozen at the start and valuing junk),
    'mid-other' (frozen, valuing no junk at the start); the head is not counted;
  - whether the chain passes a receiver (a middle agent that is a receiver).
- Per start, the set of shapes available is recorded.
- Output: counts of starts by their shape sets, a greedy and an exact smallest cover of the starts by shapes, and per
  hypergraph the number of starts.

    python3 k4/oc1cert/census_r2.py CERT_R2S.json.gz OUT.json [--sample=K] [--limit=SEC]"""
import sys, os, gzip, json, itertools, collections, time

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from cegar import Cert
from oc1_mc2_rand import Inst
import verify_r2 as VR


def shapes_at(sets, vals, Y):
    I = Inst(sets, vals); n = I.n
    sts, frozen = VR.canonical_states(I, Y)
    J = [g for g in range(I.m) if g not in Y]
    D = {j for j in range(n) if frozen[j] and any(g in I.R[j] for g in J)}
    out = set()
    for x0, nb, p, hs in sts:
        if not I.one_absorber([list(b) for b in nb]): continue
        pos = set()
        if hs[len(p) - 1]: pos.add('end')
        for i in range(1, len(p) - 1):
            if hs[i]:
                a = p[i]
                pos.add('mid-receiver' if not frozen[a] else 'mid-dangerous' if a in D else 'mid-other')
        passes = any(not frozen[p[i]] for i in range(1, len(p) - 1))
        out.add((tuple(sorted(pos)) or ('head only',), passes))
    return out


def cover(universe_sets):
    """greedy and exact smallest sets of shapes hitting every start's shape set"""
    shapes = sorted(set().union(*universe_sets)) if universe_sets else []
    greedy, left = [], list(universe_sets)
    while left:
        best = max(shapes, key=lambda s: sum(s in u for u in left))
        greedy.append(best); left = [u for u in left if best not in u]
    for r in range(1, len(greedy) + 1):
        for c in itertools.combinations(shapes, r):
            if all(any(s in u for s in c) for u in universe_sets): return greedy, list(c)
    return greedy, greedy


def main():
    src, out = sys.argv[1], sys.argv[2]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[3:] if a.startswith('--') and '=' in a)
    sample = int(opt.get('sample', 1)); limit = float(opt['limit']) if 'limit' in opt else None
    print('$ python3 k4/oc1cert/census_r2.py', *sys.argv[1:], flush=True)
    recs = [r for r in json.load(gzip.open(src))['cores'] if r['result'] != 'certified']
    T = collections.Counter(); per = []; allsets = []; t0 = time.time()
    for r in recs:
        C = Cert(r['sets'], r2='s'); st = C.run(max_fail=10 ** 9, time_limit=limit)
        complete = st == 'FAIL'
        cnt = collections.Counter()
        for k, (prof, Y) in enumerate(C.fails):
            if k % sample: continue
            vals = [list(C.dom[i][t]) for i, t in enumerate(prof)]
            sh = shapes_at(r['sets'], vals, tuple(Y))
            key = frozenset(sh)
            cnt[key] += 1; allsets.append(key)
            if not sh: T['NO R2-C REPAIR (should not happen)'] += 1
        T['starts analysed'] += sum(cnt.values()); T['starts where (S) fails'] += len(C.fails)
        T['hypergraphs complete' if complete else 'hypergraphs cut by the time limit'] += 1
        per.append({'list': r['list'], 'idx': r['idx'], 'm': 1 + max(max(s) for s in r['sets']), 'sets': r['sets'],
                    'complete': complete, 'starts': len(C.fails),
                    'shape sets': [[sorted([list(a), b] for a, b in k), c] for k, c in cnt.most_common()]})
        print(r['list'], r['idx'], 'starts', len(C.fails), 'complete' if complete else 'partial',
              '%.0f s' % (time.time() - t0), flush=True)
    tot = collections.Counter(allsets)
    shapes = collections.Counter(s for u in allsets for s in u)
    g, ex = cover(list(set(allsets)))
    res = {'what': "census of R2-C repair shapes at the hard starts with >= 2 receivers where (S) fails, n = 4",
           'totals': dict(T),
           'starts per shape (a start counts for every shape it has)': [[list(a), b, c] for (a, b), c in shapes.most_common()],
           'starts per shape set': [[sorted([list(a), b] for a, b in k), c] for k, c in tot.most_common()],
           'greedy cover': [[list(a), b] for a, b in g], 'smallest cover': [[list(a), b] for a, b in ex],
           'per hypergraph': per}
    json.dump(res, open(out, 'w'), indent=1)
    for k in sorted(T): print(k, T[k])
    print('starts per shape:'); [print('  ', a, 'passes a receiver' if b else 'no middle receiver', c) for (a, b), c in shapes.most_common()]
    print('smallest cover:', [(a, b) for a, b in ex])
    print('wrote', out, '%.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main()
