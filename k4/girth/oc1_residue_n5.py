"""The n = 5 RF residue classes DEMOTE-0 (|U'| = 1, D_T' empty) and (1, 3) (|U'| = 1, |D_T'| = 3), taken from the
certifier's n = 5 failure exports (two_move_starts_n5_partial6.json.gz and two_move_starts_n5_sel2.json.gz on
compute/k4-oc1max-cert; partial lists), split with the oc1-hall session (k4/oc1_hall.md §24.9 on claude/k4-oc1-hall).

Pass 1 (build): for every start, every order the export lists for it and every receiver u: Y' = SD(u, o - u); the
distinct (hypergraph, profile, Y') with a maximum matching and one receiver are classified by |D_T'|; the starts of
DEMOTE-0 and (1, 3) are written to OUT.jsonl.gz with the RF path.
Pass 2 (check): Lemma DEMOTE's uniform statement (k4/girth/oc1_residue.check_one: (i) w or d owns; (T); (C); (C'))
on every stored start, and candidate uniform repairs (see below), with raw EFX0 (k4/sdc/oc1_mc2_rand.Inst).

    python3 k4/girth/oc1_residue_n5.py build EXPORT1 EXPORT2 ... OUT.jsonl.gz [JOBS]
    python3 k4/girth/oc1_residue_n5.py check OUT.jsonl.gz [JOBS]
EVIDENCE (partial exports; the starts themselves are the certifier's, re-checked raw on samples by oc1_demote_n5.py).
"""
import collections
import gzip
import itertools
import json
import multiprocessing as mp
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_r2n5 import path_from  # noqa: E402


def build_job(task):
    name, sets, starts = task
    n = len(sets)
    R = [set(s) for s in sets]
    out, C = [], collections.Counter()
    seen = set()
    for st in starts:
        vals = st['vals']
        v = [dict(zip(sets[i], vals[i])) for i in range(n)]
        Y = tuple(st['picks'])
        rl, J = roles(sets, vals, list(Y))
        recv = [i for i in range(n) if rl[i] == 'U']
        for o in st['orders']:
            for u in recv:
                Y2 = sd(R, v, [u] + [a for a in o if a != u])
                if None in Y2:
                    C['RF picks not perfect'] += 1
                    continue
                key = (tuple(map(tuple, vals)), Y2)
                if key in seen:
                    continue
                seen.add(key)
                rl2, J2 = roles(sets, vals, list(Y2))
                nU, nDT = rl2.count('U'), rl2.count('DT')
                cls = 'R2' if nU >= 2 else ('U1' if nDT == 1 else '(1, %d)' % nDT)
                C['distinct RF starts ' + cls] += 1
                if nU == 1 and nDT in (0, 3):
                    path = path_from(Y, Y2, J, u)
                    out.append(dict(h=name, sets=sets, vals=vals, Y=list(Y), Y2=list(Y2), u=u, path=path,
                                    cls='DEMOTE-0' if nDT == 0 else '(1, 3)'))
    return out, C


def main_build(exports, outp, jobs):
    tasks = []
    for f in exports:
        d = json.load(gzip.open(f))
        for h in d['hypergraphs']:
            name = '%s#%d' % (h['list'], h['idx'])
            for i in range(0, len(h['starts']), 2000):
                tasks.append((name, h['sets'], h['starts'][i:i + 2000]))
    C = collections.Counter()
    keys = set()
    t0 = time.time()
    with gzip.open(outp, 'wt') as fo, mp.Pool(jobs) as pool:
        for k, (out, c) in enumerate(pool.imap_unordered(build_job, tasks)):
            C.update(c)
            for r in out:
                key = (r['h'], tuple(map(tuple, r['vals'])), tuple(r['Y2']))
                if key in keys:
                    continue
                keys.add(key)
                C['stored ' + r['cls']] += 1
                fo.write(json.dumps(r) + '\n')
            if (k + 1) % 100 == 0:
                print('  ... %d of %d chunks, %.0f s' % (k + 1, len(tasks), time.time() - t0), flush=True)
    print('build: (distinct per chunk; the stored counts are global)')
    for k in sorted(C):
        print('   %-50s %8d' % (k, C[k]))


def candidate_repairs(I, sets, vals, Y, Y2, u, path, rl2, J2):
    """explicit completions tried at Y' (raw EFX0): returns the names of those that are EFX0"""
    n = len(sets)
    v = I.v
    d = path[-1]
    w = path[1] if len(path) > 1 else d
    base = [[p] for p in Y2]
    J2 = sorted(J2)
    ok = []
    # A1 form (oc1-hall's Lemma RF-A1): w takes Y'_w + (J' - h), d takes Y'_d + h, h = d's favourite good of J'
    Jd = [g for g in J2 if g in v[d]]
    if w != d and Jd:
        h = max(Jd, key=lambda g: v[d][g])
        B = [list(b) for b in base]
        B[w] += [g for g in J2 if g != h]
        B[d].append(h)
        if I.efx0(B):
            ok.append('A1 form: w takes J\' - h, d takes h (d\'s favourite junk)')
    # owner d takes all junk but its favourite... and simple variants
    for own, tag in ((w, 'w'), (d, 'd')):
        for g in J2:
            for r in range(n):
                if r == own:
                    continue
                B = [list(b) for b in base]
                B[own] += [x for x in J2 if x != g]
                B[r].append(g)
                if I.efx0(B):
                    ok.append('owner %s takes all junk but one, which goes to one other agent' % tag)
                    break
            else:
                continue
            break
    return ok


def trade_then_singles(I, Y2, d, rl2, J2):
    """some trade (T) of d with a pick-dangerous p (p takes {Y'_d, j}, d takes Y'_p, both improve) after which every
    remaining junk good goes to a different agent (no absorber) and the allocation is EFX0"""
    from oc1_rf_owner import owner_ok
    n = len(Y2)
    v = I.v
    base = [[p] for p in Y2]
    for p in range(n):
        if rl2[p] != 'Dp':
            continue
        for j in J2:
            if j not in v[p]:
                continue
            if not (I.V(p, [Y2[d], j]) > I.V(p, [Y2[p]]) and I.V(d, [Y2[p]]) > I.V(d, [Y2[d]])):
                continue
            st = [list(b) for b in base]
            st[p] = [Y2[d], j]
            st[d] = [Y2[p]]
            if owner_ok(I, st, None):
                return True
    return False


def chain_then_d_absorbs(I, Y2, d, rl2, J2):
    """oc1-hall's RF-B shape, any number of truly dangerous agents: some k in D_T' takes an improving junk set H, and d
    takes Y'_k, Y'_d and the rest of the junk; EFX0 at once"""
    n = len(Y2)
    v = I.v
    for k in range(n):
        if rl2[k] != 'DT' or k == d:
            continue
        Jk = [g for g in J2 if g in v[k]]
        for r in range(1, len(Jk) + 1):
            for H in itertools.combinations(Jk, r):
                if not I.V(k, H) > I.V(k, [Y2[k]]):
                    continue
                B = [[p] for p in Y2]
                B[k] = list(H)
                B[d] = [Y2[k], Y2[d]] + [g for g in J2 if g not in H]
                if I.efx0(B):
                    return True
    return False


def w_chain_shape(I, Y2, d, w, J2):
    """(1, 3) shape: w (truly dangerous at Y') takes an improving junk pair H, d takes Y'_w; then d takes its old
    good Y'_d and one junk good x, and w takes one more junk good y (or the same with d and w exchanged); every junk
    good placed, EFX0 at once"""
    v = I.v
    Jw = [g for g in J2 if g in v[w]]
    for H in itertools.combinations(Jw, 2):
        if not I.V(w, H) > I.V(w, [Y2[w]]):
            continue
        rest = [g for g in J2 if g not in H]
        for x in rest:
            for y in rest:
                if x == y and len(rest) > 1:
                    continue
                for a, b in ((d, w), (w, d)):
                    B = [[p] for p in Y2]
                    B[w] = list(H)
                    B[d] = [Y2[w]]
                    B[a] += [Y2[d], x]
                    left = [g for g in rest if g != x]
                    if len(left) > 1 or (left and left[0] != y):
                        continue
                    B[b] += left
                    if I.efx0(B):
                        return True
    return False


def check_job(lines):
    from oc1_mc2_rand import Inst
    from oc1_residue import check_one
    C = collections.Counter()
    fails = []
    for line in lines:
        r = json.loads(line)
        sets, vals, Y, Y2, u, path = r['sets'], r['vals'], tuple(r['Y']), tuple(r['Y2']), r['u'], r['path']
        n = len(sets)
        R = [set(s) for s in sets]
        v = [dict(zip(sets[i], vals[i])) for i in range(n)]
        top = max(R[u], key=lambda g: v[u][g])
        w = Y.index(top) if top in Y and Y.index(top) != u else path[-1]
        cls, verdict = check_one(sets, vals, Y2, w, path[-1])
        tag = r['cls']
        if verdict.startswith('(T)') or verdict.startswith('(C)'):
            from oc1_mc2_rand import Inst as _I
            I0 = _I(sets, vals)
            rl2_, J2_ = roles(sets, vals, list(Y2))
            if verdict.startswith('(T)'):
                C[(tag, '(T) cases: a trade after which every junk good goes to a different agent')] += \
                    trade_then_singles(I0, Y2, path[-1], rl2_, sorted(J2_))
            else:
                C[(tag, '(C) cases: RF-B shape (k takes H, d takes Y\'_k, Y\'_d and the rest)')] += \
                    chain_then_d_absorbs(I0, Y2, path[-1], rl2_, sorted(J2_))
                if len(path) == 3 and rl2_[path[1]] == 'DT':
                    C[(tag, "(C) cases: w-chain shape (w takes a junk pair, d takes Y'_w; d: old Y'_d + x, w: + y)")] += \
                        w_chain_shape(I0, Y2, path[-1], path[1], sorted(J2_))
        C[(tag, 'starts')] += 1
        C[(tag, 'path length %d, d ends with %s' % (len(path) - 1, 'junk' if Y2[path[-1]] not in Y else "u's old pick" if Y2[path[-1]] == Y[u] else 'a pick'))] += 1
        C[(tag, 'DEMOTE: ' + (verdict.split(' (')[0] if verdict.startswith('FAILS') else verdict))] += 1
        if verdict.startswith('FAILS') and len(fails) < 3:
            fails.append(r)
        I = Inst(sets, vals)
        rl2, J2 = roles(sets, vals, list(Y2))
        for name in candidate_repairs(I, sets, vals, Y, Y2, u, path, rl2, J2):
            C[(tag, 'explicit: ' + name)] += 1
    return C, fails


def main_check(inp, jobs):
    lines = gzip.open(inp, 'rt').read().splitlines()
    chunks = [lines[i:i + 500] for i in range(0, len(lines), 500)]
    C = collections.Counter()
    F = []
    t0 = time.time()
    with mp.Pool(jobs) as pool:
        for k, (c, f) in enumerate(pool.imap_unordered(check_job, chunks)):
            C.update(c)
            F += f
            if (k + 1) % 20 == 0:
                print('  ... %d of %d chunks, %.0f s' % (k + 1, len(chunks), time.time() - t0), flush=True)
    for tag in ('DEMOTE-0', '(1, 3)'):
        print(tag + ':')
        for k in sorted(k2 for t, k2 in C if t == tag):
            print('   %-90s %7d' % (k, C[(tag, k)]))
    for f in F[:3]:
        print('DEMOTE FAILS at', json.dumps(f))
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    print('$ python3 k4/girth/oc1_residue_n5.py', *[os.path.basename(a) for a in sys.argv[1:]], flush=True)
    if sys.argv[1] == 'build':
        args = sys.argv[2:]
        jobs = int(args[-1]) if args[-1].isdigit() else 2
        if args[-1].isdigit():
            args = args[:-1]
        main_build(args[:-1], args[-1], jobs)
    else:
        main_check(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 2)
