"""The repairing moves at the two RF classes of the coordinator's task (k4/ttc.md §14.8): class (|U'|, |D_T'|) = (1, 3)
and DEMOTE-0 = (1, 0) starts whose picks do not complete (dumped by rf_classes_n5.py).

For each start, every official move (de_free chains and additions with their paths, ttclib.iter_chains_path; rings as
states, de_free.moves with rings allowed) is tested for a one-absorber completion (oc_absorb.extends_A).  A repairing
chain is described by:
  - the head x_0's role: in D_T' (truly dangerous), dangerous, frozen, or the receiver;
  - x_0's new base H_0: how many junk goods, how many of the truly dangerous agents value each of them, and whether it
    contains the end's pick y_{x_t};
  - the path: length, whether it is a pure want path (every x_i, i >= 1, takes exactly x_{i-1}'s pick), whether it
    passes the receiver before its end, whether the end is the receiver, and which middle agents take junk;
  - whether x_1 wants y_{x_0} (canonical).
Per start, the set of shapes is recorded; counts by shape, and the smallest cover of the starts by shapes (greedy).

    python3 k4/ttc/rf_canon.py DUMP.jsonl CLASS   (CLASS: 1,3 or 1,0)"""
import sys, os, json, collections, itertools, multiprocessing as mp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ttclib as T


def shape(E, b, b2, path, DT, U, D):
    B = T.bundles(E, b); J = set(g for g in range(E.m) if b[g] < 0); x0 = path[0]
    role = 'D_T' if x0 in DT else 'dangerous' if x0 in D else 'receiver' if x0 in U else 'frozen'
    if len(path) == 1:
        return ('addition by %s' % role,)
    H0 = [g for g in range(E.m) if b2[g] == x0]
    hj = [g for g in H0 if g in J]
    share = tuple(sorted(sum(1 for k in DT if E.v[k].get(g, 0) > 0) for g in hj))
    has_end = any(g in B[path[-1]] for g in H0)
    pure = all(sorted(g for g in range(E.m) if b2[g] == path[i]) == sorted(B[path[i - 1]]) for i in range(1, len(path)))
    mids = []
    for i in range(1, len(path)):
        extra = set(g for g in range(E.m) if b2[g] == path[i]) - set(B[path[i - 1]])
        if extra:
            a = path[i]
            mids.append(('end' if i == len(path) - 1 else 'mid') + '-' +
                        ('D_T' if a in DT else 'dangerous' if a in D else 'receiver' if a in U else 'frozen'))
    canon = E.v[path[1]].get(B[x0][0], 0) > T.val(E, path[1], B[path[1]]) if len(B[x0]) == 1 else False
    passes = any(x in U for x in path[1:-1])
    return ('chain', 'head %s' % role, 'canonical' if canon else 'non-canonical', 'len %d' % (len(path) - 1),
            'H0 junk %d shared-by %s%s' % (len(hj), share, ' + end pick' if has_end else ''),
            'pure want path' if pure else 'junk past the head at %s' % sorted(set(mids)),
            'end %s' % ('receiver' if path[-1] in U else 'frozen'), 'passes the receiver' if passes else '')


def analyse(r):
    sets, vals, Y = r['sets'], r['vals'], tuple(r['picks']); m = 1 + max(max(s) for s in sets)
    E = T.Enc(sets, vals, m); b = T.base_of(E, Y); DT = set(r['DT']); U = set(r['U']); D = T.dangerous_set(E, b)
    shapes = set(); chain_states = set()
    for b2, path in T.iter_chains_path(E, b):
        chain_states.add(b2)
        if T.extends_A(E, b2, 1):
            shapes.add(shape(E, b, b2, path, DT, U, D))
    T.DF.CHAIN_ONLY = False
    try:
        for b2 in T.DF.moves(E, b):
            if b2 not in chain_states and T.extends_A(E, b2, 1):
                shapes.add(('ring',))
    finally:
        T.DF.CHAIN_ONLY = True
    return r, sorted(shapes)


if __name__ == '__main__':
    print('$ python3 k4/ttc/rf_canon.py', *sys.argv[1:], flush=True)
    want = [int(x) for x in sys.argv[2].split(',')]
    rows = [json.loads(l) for l in open(sys.argv[1]) if json.loads(l)['class'] == want]
    print('starts', len(rows), flush=True)
    C = collections.Counter(); per = []
    with mp.Pool() as pool:
        for r, shapes in pool.imap_unordered(analyse, rows, chunksize=8):
            per.append(set(shapes))
            if not shapes:
                C['NO REPAIRING MOVE'] += 1; print('NO MOVE', json.dumps(r)); continue
            for s in shapes:
                C[s] += 1
    print('shapes (number of starts having each):')
    for s, c in C.most_common():
        print('  %6d  %s' % (c, ' | '.join(x for x in s if x) if isinstance(s, tuple) else s))
    # greedy cover of the starts by shapes
    left = [p for p in per if p]; cover = []
    while left:
        cnt = collections.Counter(s for p in left for s in p)
        best, c = cnt.most_common(1)[0]; cover.append((best, c)); left = [p for p in left if best not in p]
    print('greedy cover:')
    for s, c in cover:
        print('  %6d  %s' % (c, ' | '.join(x for x in s if x)))
