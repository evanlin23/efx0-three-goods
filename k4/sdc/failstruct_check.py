"""A first completeness check of k3-oc1's draft Theorem FAIL-STRUCT (k4/k3_oc1.md §13.7), with the coordinator's
literal reading of the three shapes, on every OC1^max-failing start of the complete n = 4 export (and optionally an
n = 5 export).  Definitions at the picks Y (junk J):
  frozen: a single-pick holder whose pick some other agent prefers to its own;
  dangerous (D): frozen and values some junk good;  truly dangerous (D_T): frozen and v(J) > v(pick).
Shapes:
  S1  two agents x != y in D_T and a pair {g, h} of junk with v_x(g)+v_x(h) > p_x and v_y(g)+v_y(h) > p_y;
  S2  a dangerous x and a receiver u with v_x(Y_u) > 0 and v_u(Y_x) > 0;
  S3  two dangerous x != y, a junk good j and a third agent z with v(j) + v(Y_z) > p for both x and y.
  S1' (generalized S1) two agents x != y in D_T with intersecting minimal junk sets H_x, H_y (v_x(H_x) > p_x, etc.).
Reports the coverage by S1 / S2 / S3 and the starts covered by none, plus |D|, |D_T| and the receiver counts.
    python3 k4/sdc/failstruct_check.py FILE [STRIDE]      (FILE: an export .json.gz, or a .jsonl.gz of starts)"""
import sys, gzip, json, itertools, collections, multiprocessing as mp
import _paths  # noqa: F401
from oc1_mc2_rand import Inst


def job(a):
    sets, vals, Y = a
    I = Inst(sets, vals); n = I.n; Y = tuple(Y)
    J = [g for g in range(I.m) if g not in Y]
    p = [I.v[i].get(Y[i], 0) if Y[i] is not None else 0 for i in range(n)]
    want = lambda i, g: I.v[i].get(g, 0) > p[i]
    frozen = [j for j in range(n) if Y[j] is not None and any(i != j and want(i, Y[j]) for i in range(n))]
    rec = [u for u in range(n) if Y[u] is not None and u not in frozen]
    D = [j for j in frozen if any(I.v[j].get(g, 0) > 0 for g in J)]
    DT = [j for j in frozen if sum(I.v[j].get(g, 0) for g in J) > p[j]]
    s1 = any(I.v[x].get(g, 0) + I.v[x].get(h, 0) > p[x] and I.v[y].get(g, 0) + I.v[y].get(h, 0) > p[y]
             for x, y in itertools.combinations(DT, 2) for g, h in itertools.combinations(J, 2))
    s2 = any(I.v[x].get(Y[u], 0) > 0 and I.v[u].get(Y[x], 0) > 0 for x in D for u in rec)
    s3 = any(all(I.v[w].get(j, 0) + I.v[w].get(Y[z], 0) > p[w] for w in (x, y))
             for x, y in itertools.combinations(D, 2) for j in J for z in range(n) if z not in (x, y) and Y[z] is not None)
    def mins(x):  # minimal junk sets threatening x (v_x(H) > p_x)
        out = []
        for r in range(1, len(J) + 1):
            for H in itertools.combinations(J, r):
                if sum(I.v[x].get(g, 0) for g in H) > p[x] and not any(set(M) <= set(H) for M in out):
                    out.append(H)
        return out
    MS = {x: mins(x) for x in DT}
    s1p = any(set(a) & set(b) for x, y in itertools.combinations(DT, 2) for a in MS[x] for b in MS[y])
    C = collections.Counter()
    C["S1' (two D_T agents with intersecting minimal threatening junk sets): %s" % s1p] += 1
    C['starts'] += 1; C['|D|=%d |D_T|=%d receivers=%d' % (len(D), len(DT), len(rec))] += 1
    key = ''.join(s for s, b in (('S1', s1), ('S2', s2), ('S3', s3)) if b) or 'NONE'
    C['with S1\' : ' + (''.join(s for s, b in (("S1'", s1p), ('S2', s2), ('S3', s3)) if b) or 'NONE')] += 1
    C['shapes ' + key] += 1
    return C, (None if key != 'NONE' else (sets, vals, Y, len(D), len(DT), len(rec)))


if __name__ == '__main__':
    print('$ python3 k4/sdc/failstruct_check.py', *sys.argv[1:], flush=True)
    S = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    if sys.argv[1].endswith('.jsonl.gz'):  # one start per line with sets, vals, picks (e.g. d1's off-export walk dump)
        tasks = [(r['sets'], r['vals'], r['picks']) for r in map(json.loads, gzip.open(sys.argv[1], 'rt'))][::S]
    else:
        d = json.load(gzip.open(sys.argv[1]))
        tasks = [(h['sets'], st['vals'], st['picks']) for h in d['hypergraphs'] for st in h['starts']][::S]
    T = collections.Counter(); shown = 0
    with mp.Pool() as pool:
        for C, ex in pool.imap_unordered(job, tasks, chunksize=64):
            T.update(C)
            if ex and shown < 3: shown += 1; print('UNCOVERED', json.dumps(ex), flush=True)
    for k in sorted(T): print(k, T[k])
