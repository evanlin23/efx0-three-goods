"""The SINK form of Lemma DEMOTE (k4/girth.md section 7; proposed jointly with the oc1-hall session): at every RF start
Y' with maximum-matching picks, Y' or the state after one DEMOTE move ((T)/(T*) rings through a receiver with one junk
good added, (C)/(C') 2-agent chains from a truly dangerous agent) has a complete EFX0 allocation in which all the
remaining junk goes to one agent a in {w, d}, except at most one junk good, which goes to one other agent.

Checked (raw EFX0, k4/sdc/oc1_mc2_rand.Inst) on every distinct RF start of the complete n = 4 export, and on the n = 5
residue classes DEMOTE-0 and (1, 3) of the full exports (RESIDUE.jsonl.gz from k4/girth/oc1_residue_n5.py).

    python3 k4/girth/oc1_sink.py RESIDUE.jsonl.gz [JOBS]
    python3 k4/girth/oc1_sink.py stream EXPORT1 EXPORT2 ... STRIDE JOBS   (n = 5 R2 and U1 classes, every STRIDE-th start)
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
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_r2n5 import path_from  # noqa: E402


def subsets(xs, kmin=0):
    for r in range(kmin, len(xs) + 1):
        yield from itertools.combinations(xs, r)


def demote_moves(I, Y2, rl2, J2, d):
    """the states after the DEMOTE moves (T), (T*), (C), (C'): (state, junk left)"""
    n = len(Y2)
    v = I.v
    base = [[p] for p in Y2]
    U = [i for i in range(n) if rl2[i] == 'U']
    for r in U:
        for c1 in range(n):
            if c1 == r or rl2[c1] != 'Dp':
                continue
            for j in J2:
                if j not in v[c1] or not I.V(c1, [Y2[r], j]) > I.V(c1, [Y2[c1]]):
                    continue
                if I.V(r, [Y2[c1]]) > I.V(r, [Y2[r]]):            # (T)
                    st = [list(b) for b in base]
                    st[c1] = [Y2[r], j]
                    st[r] = [Y2[c1]]
                    yield '(T)', st, [g for g in J2 if g != j]
                for c2 in range(n):                                 # (T*)
                    if c2 in (r, c1):
                        continue
                    if I.V(c2, [Y2[c1]]) > I.V(c2, [Y2[c2]]) and I.V(r, [Y2[c2]]) > I.V(r, [Y2[r]]):
                        st = [list(b) for b in base]
                        st[c1] = [Y2[r], j]
                        st[c2] = [Y2[c1]]
                        st[r] = [Y2[c2]]
                        yield '(T*)', st, [g for g in J2 if g != j]
    for k in range(n):
        if rl2[k] != 'DT':
            continue
        for H in subsets([g for g in J2 if g in v[k]], 1):
            if not I.V(k, H) > I.V(k, [Y2[k]]):
                continue
            for h in range(n):
                if h == k:
                    continue
                rest = [g for g in J2 if g not in H and g in v[h]]
                for Hh in subsets(rest):
                    if I.V(h, [Y2[k]] + list(Hh)) > I.V(h, [Y2[h]]):
                        st = [list(b) for b in base]
                        st[k] = list(H)
                        st[h] = [Y2[k]] + list(Hh)
                        left = [g for g in J2 if g not in H and g not in Hh] + [Y2[h]]
                        yield '(C)' if h == d else "(C')", st, left


def sink_ok(I, st, left, a):
    """all of `left` to a, except at most one good to one other agent; EFX0"""
    n = len(st)
    B = [list(b) for b in st]
    B[a] += left
    if I.efx0(B):
        return True
    for g in left:
        for o in range(n):
            if o == a:
                continue
            B = [list(b) for b in st]
            B[a] += [x for x in left if x != g]
            B[o].append(g)
            if I.efx0(B):
                return True
    return False


def check(sets, vals, Y, Y2, u, path):
    I = Inst(sets, vals)
    rl2, J2 = roles(sets, vals, list(Y2))
    J2 = sorted(J2)
    d = path[-1]
    w = path[1] if len(path) > 1 else d
    base = [[p] for p in Y2]
    nU, nDT = rl2.count('U'), rl2.count('DT')
    cls = 'R2' if nU >= 2 else ('U1' if nDT == 1 else '(1, %d)' % nDT)
    for a in sorted({w, d}):
        if sink_ok(I, base, J2, a):
            return cls, 'at Y\', absorber %s' % ('d' if a == d else 'w')
    for kind, st, left in demote_moves(I, Y2, rl2, J2, d):
        for a in sorted({w, d}):
            if sink_ok(I, st, left, a):
                return cls, 'after %s, absorber %s' % (kind, 'd' if a == d else 'w')
    return cls, 'FAILS'


def job_n4(task):
    sets, starts = task
    n = len(sets)
    R = [set(s) for s in sets]
    C = collections.Counter()
    seen = set()
    fails = []
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
            cls, verdict = check(sets, vals, Y, Y2, u, path_from(Y, Y2, J, u))
            C[('n=4', cls, verdict)] += 1
            if verdict == 'FAILS' and len(fails) < 3:
                fails.append((sets, vals, Y, Y2))
    return C, fails


def job_n5(lines):
    C = collections.Counter()
    fails = []
    for line in lines:
        r = json.loads(line)
        cls, verdict = check(r['sets'], r['vals'], tuple(r['Y']), tuple(r['Y2']), r['u'], r['path'])
        C[('n=5', r['cls'], verdict)] += 1
        if verdict == 'FAILS' and len(fails) < 3:
            fails.append(r)
    return C, fails


def job_stream(task):
    """n = 5 exports, streaming: every start of the chunk (every STRIDE-th), every listed order, every receiver; SINK
    on the R2 and U1 classes"""
    name, sets, starts, stride = task
    n = len(sets)
    R = [set(s) for s in sets]
    C = collections.Counter()
    fails = []
    seen = set()
    for t, st in enumerate(starts):
        if t % stride:
            continue
        vals = st['vals']
        v = [dict(zip(sets[i], vals[i])) for i in range(n)]
        Y = tuple(st['picks'])
        rl, J = roles(sets, vals, list(Y))
        recv = [i for i in range(n) if rl[i] == 'U']
        for o in st['orders']:
            for u in recv:
                Y2 = sd(R, v, [u] + [a for a in o if a != u])
                key = (tuple(map(tuple, vals)), Y2)
                if None in Y2 or key in seen:
                    continue
                seen.add(key)
                rl2, _ = roles(sets, vals, list(Y2))
                if not (rl2.count('U') >= 2 or rl2.count('DT') == 1):
                    continue
                cls, verdict = check(sets, vals, Y, Y2, u, path_from(Y, Y2, J, u))
                C[('n=5', cls, verdict)] += 1
                if verdict == 'FAILS' and len(fails) < 3:
                    fails.append((name, sets, vals, Y, Y2))
    return C, fails


def main_stream(exports, stride, jobs):
    tasks = []
    for f in exports:
        d = json.load(gzip.open(f))
        for h in d['hypergraphs']:
            for i in range(0, len(h['starts']), 2000):
                tasks.append(('%s#%d' % (h['list'], h['idx']), h['sets'], h['starts'][i:i + 2000], stride))
    C = collections.Counter()
    F = []
    with mp.Pool(jobs) as pool:
        for c, f in pool.imap_unordered(job_stream, tasks):
            C.update(c)
            F += f
    for k in sorted(C):
        print('   %-6s %-10s %-34s %8d' % (k[0], k[1], k[2], C[k]))
    for f in F[:5]:
        print('SINK FAILS at', f)
    sys.stdout.flush()


def main():
    if sys.argv[1] == 'stream':
        print('$ python3 k4/girth/oc1_sink.py stream', *[os.path.basename(a) for a in sys.argv[2:]], flush=True)
        main_stream(sys.argv[2:-2], int(sys.argv[-2]), int(sys.argv[-1]))
        return
    inp = sys.argv[1]
    jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    print('$ python3 k4/girth/oc1_sink.py', os.path.basename(inp), jobs, flush=True)
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    tasks = [(h['sets'], h['starts'][i:i + 400]) for h in d['hypergraphs'] for i in range(0, len(h['starts']), 400)]
    lines = gzip.open(inp, 'rt').read().splitlines()
    chunks = [lines[i:i + 500] for i in range(0, len(lines), 500)]
    C = collections.Counter()
    F = []
    with mp.Pool(jobs) as pool:
        for c, f in pool.imap_unordered(job_n4, tasks):
            C.update(c)
            F += f
        for c, f in pool.imap_unordered(job_n5, chunks):
            C.update(c)
            F += f
    for k in sorted(C):
        print('   %-6s %-10s %-34s %8d' % (k[0], k[1], k[2], C[k]))
    for f in F[:5]:
        print('SINK FAILS at', f)
    sys.stdout.flush()


if __name__ == '__main__':
    main()
