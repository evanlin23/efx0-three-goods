"""The shape of the two-chain repairs at OC1 failures with one unfrozen pick holder z (k4/oc1max_multi.md §8).

For every repairing pair (P1, P2) with P1 a canonical chain from k in D at the picks and P2 a canonical chain at B1
ending at z (lift.py's shape), record:
  pair     : P1's improving set is a junk pair valued above its pick by another dangerous agent (a shared pair);
  top      : z holds its top good of R_z after P2;
  two-picks: P2's first agent q takes both goods z vacated: its pick Y_z and its good a1 after P1;
  A1       : q takes a1 (z's good after P1), whatever else;
  owner    : the S* owners after P2 include k, z, q, or only others; or only a non-S* one-absorber completion exists.
Counts are over starts (some repairing pair of each kind), on a file of failing starts (walk_fail.py output).

    python3 k4/oc1max_multi/lift_shape.py FILE.jsonl
"""
import sys, os, json, collections, multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from mmlib import Inst, base_from_picks, junk, frozen, dangerous, oa_absorbers, moves, is_canonical, sstar_owners
from lift import canon_at


def study(rec):
    I = Inst(rec['sets'], rec['vals']); Y = tuple(rec['picks']); b = base_from_picks(Y)
    J = junk(I, b); D = dangerous(I, b); F = set(frozen(I, b)); p = [I.V(i, b[i]) for i in range(I.n)]
    U = [i for i in range(I.n) if i not in F and b[i]]
    if len(U) != 1: return rec, {'not one unfrozen pick holder'}
    z = U[0]; top = max(I.R[z], key=lambda g: I.rk(z, g)); st = set()
    for B1, ds1 in moves(I, b).items():
        c1 = [d for d in ds1 if is_canonical(I, b, d, D)]
        if not c1: continue
        for B2, ds2 in moves(I, B1).items():
            c2 = [d for d in ds2 if canon_at(I, B1, d) and d[1][-1] == z]
            if not c2 or not oa_absorbers(I, B2): continue
            ss = sstar_owners(I, B2)
            for d1 in c1:
                k = d1[1][0]; H0 = set(B1[k])
                pair = len(H0) == 2 and H0 <= set(J) and any(q != k and I.V(q, H0) > p[q] for q in D)
                for d2 in c2:
                    q = d2[1][0]; tags = []
                    if pair: tags.append('pair')
                    if top in B2[z]: tags.append('top')
                    if set(B1[z]) | set(b[z]) <= set(B2[q]): tags.append('two-picks')
                    if set(B1[z]) <= set(B2[q]): st.add('A1: q absorbs a1')
                    if set(B1[z]) <= set(B2[q]) and (pair or set(b[z]) <= set(B1[k])):
                        st.add('A1 and P1 absorbs a shared pair or Y_z')
                    own = ('k' if k in ss else '') + ('z' if z in ss else '') + ('q' if q in ss else '')
                    tags.append('owner ' + (own or ('other S*' if ss else 'non-S* only')))
                    st.add(' + '.join(tags))
                    if pair and top in B2[z] and 'two-picks' in tags: st.add('PAIR+TOP+TWO-PICKS')
    return rec, st


if __name__ == '__main__':
    import gzip
    recs = [json.loads(l) for l in (gzip.open(sys.argv[1], 'rt') if sys.argv[1].endswith('.gz') else open(sys.argv[1]))]
    T = collections.Counter(); missing = None
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for rec, st in pool.imap_unordered(study, recs, chunksize=4):
            T['failing starts'] += 1
            for s in st: T[s] += 1
            if 'PAIR+TOP+TWO-PICKS' not in st and (missing is None or len(rec['sets']) < len(missing['sets'])): missing = rec
    print('$ python3 k4/oc1max_multi/lift_shape.py', *sys.argv[1:])
    for k in sorted(T, key=lambda k: -T[k]): print(T[k], k)
    print('a start without PAIR+TOP+TWO-PICKS:', json.dumps(missing))
