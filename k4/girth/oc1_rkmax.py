"""Do the RF residue classes occur at rank-maximal starts?  (coordinator's question for the RKMAX route, Conjecture
K4.SDC.RKMAX, k4/sdc.md §31 on claude/kind-lamport-y8fdme; definitions of its k4/sdc/extremal_rank_check.py, re-coded
here: rank_i(Y) = 1 + #{g in R_i : v_i(g) > v_i(Y_i)}, sigma(Y) = (#rank 1, ..., #rank 4), maximized
lexicographically over the maximum-matching SD pick vectors of the profile, all n! orders.)

For every distinct RF start (profile, Y') of the complete n = 4 export, by class, and every start of the n = 5 classes
DEMOTE-0 and (1, 3) (RESIDUE.jsonl.gz from k4/girth/oc1_residue_n5.py): is Y' sigma-maximal?  Also: is the failing
start Y sigma-maximal (it should not be, if RKMAX holds), and does Y' have larger sigma than Y?

    python3 k4/girth/oc1_rkmax.py RESIDUE.jsonl.gz [JOBS]
"""
import collections
import gzip
import itertools
import json
import multiprocessing as mp
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402


def sigma(sets, v, p):
    r = [1 + sum(1 for g in sets[i] if v[i][g] > v[i][p[i]]) if p[i] is not None else 5 for i in range(len(sets))]
    return tuple(sum(1 for x in r if x == k) for k in (1, 2, 3, 4))


def sigma_max(sets, v):
    R = [set(s) for s in sets]
    vecs = {sd(R, v, o) for o in itertools.permutations(range(len(sets)))}
    nu = max(sum(x is not None for x in p) for p in vecs)
    return max(sigma(sets, v, p) for p in vecs if sum(x is not None for x in p) == nu)


def classify(sets, vals, Y, Y2, cache):
    v = [dict(zip(sets[i], vals[i])) for i in range(len(sets))]
    key = tuple(map(tuple, vals))
    if key not in cache:
        cache[key] = sigma_max(sets, v)
    sm = cache[key]
    s2, s1 = sigma(sets, v, Y2), sigma(sets, v, Y)
    return s2 == sm, s1 == sm, s2 > s1


def job_n4(task):
    sets, starts = task
    n = len(sets)
    R = [set(s) for s in sets]
    C = collections.Counter()
    seen = set()
    cache = {}
    for st in starts:
        vals = st['vals']
        v = [dict(zip(sets[i], vals[i])) for i in range(n)]
        Y = tuple(st['picks'])
        rl, J = roles(sets, vals, list(Y))
        u = rl.index('U')
        for o in itertools.permutations(range(n)):
            if sd(R, v, o) != Y:
                continue
            Y2 = sd(R, v, [u] + [a for a in o if a != u])
            key = (tuple(map(tuple, vals)), Y2)
            if None in Y2 or key in seen:
                continue
            seen.add(key)
            rl2, _ = roles(sets, vals, list(Y2))
            nU, nDT = rl2.count('U'), rl2.count('DT')
            cls = 'R2' if nU >= 2 else ('U1' if nDT == 1 else '(1, %d)' % nDT)
            mx, fmx, up = classify(sets, vals, Y, Y2, cache)
            C[('n=4', cls, 'RF starts')] += 1
            C[('n=4', cls, "Y' sigma-maximal")] += mx
            C[('n=4', cls, 'failing Y sigma-maximal')] += fmx
            C[('n=4', cls, "sigma(Y') > sigma(Y)")] += up
    return C


def job_n5(lines):
    C = collections.Counter()
    cache = {}
    for line in lines:
        r = json.loads(line)
        mx, fmx, up = classify(r['sets'], r['vals'], tuple(r['Y']), tuple(r['Y2']), cache)
        C[('n=5', r['cls'], 'RF starts')] += 1
        C[('n=5', r['cls'], "Y' sigma-maximal")] += mx
        C[('n=5', r['cls'], 'failing Y sigma-maximal')] += fmx
        C[('n=5', r['cls'], "sigma(Y') > sigma(Y)")] += up
    return C


def main():
    inp = sys.argv[1]
    jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    print('$ python3 k4/girth/oc1_rkmax.py', os.path.basename(inp), jobs, flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    tasks = [(h['sets'], h['starts'][i:i + 400]) for h in d['hypergraphs'] for i in range(0, len(h['starts']), 400)]
    lines = gzip.open(inp, 'rt').read().splitlines()
    chunks = [lines[i:i + 1000] for i in range(0, len(lines), 1000)]
    C = collections.Counter()
    with mp.Pool(jobs) as pool:
        for c in pool.imap_unordered(job_n4, tasks):
            C.update(c)
        for c in pool.imap_unordered(job_n5, chunks):
            C.update(c)
    for k in sorted(C):
        print('   %-6s %-10s %-28s %8d' % (k[0], k[1], k[2], C[k]))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
