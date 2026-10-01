#!/usr/bin/env python3
"""Second implementation of the key graph of k4/sx_keygraph.py (workstream proof/k4-sx). EVIDENCE tooling.

It imports neither k4/suite/model.py nor k4/dl2_classify.py nor k4/sx_keygraph.py. The space 𝒫 is enumerated here as
every base map (each good to nobody or to one agent that values it, at most two goods per agent) with (V1), (V2)
literally; the removal-only deficit is main's k4/c4x_check.rodef (written from k4/c4x.md §1, directly, not through
Lemma H1). Keys are the frozen agents with their goods; the moves between two min-frozen states P, P' are classified
pairwise from the definitions (no generation):
  T3+  NA' = NA; exactly one changed agent x frozen in P and free in P'; exactly one z free in P and frozen in P';
       W = the changed agents frozen in both; at most one other changed agent, free in both, giving up a good of its
       base; {B'_w : w in W ∪ {z}} = {B_w : w in W ∪ {x}} as sets of bases, and B'_z ⊆ N_z(B_z);
  T3   T3+ with W empty;   T4   every changed agent frozen in P and in P', NA' = NA.
For every profile it prints the keys with def* and, for each key with def* > 0, whether DLK holds for the edge sets
T3, T3+, T3T4, T3+T4 (as k4/sx_keygraph.py).

usage: python3 k4/sx_xcheck.py DUMP.jsonl.gz [--every=E] [--mmax=M]   compare with the per-key records of a sx_keygraph
       dump (or, for a k4/sx_hunt.py dump, with sx_keygraph.run_one)
       python3 k4/sx_xcheck.py catalog FILE [--every=E] [--max=N]   compare with sx_keygraph.run_one on the same profiles
       (the second form imports k4/sx_keygraph.py only to compare, after this module has computed its own verdicts)"""
import collections, gzip, itertools, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import c4x_check as CX

EDGESETS = ('T3', 'T3+', 'T3T4', 'T3+T4')


def val(vl, S): return sum(vl.get(g, 0) for g in S)


def keygraph(sets, vals, m):
    n = len(sets)
    vl = [dict(zip(S, V)) for S, V in zip(sets, vals)]
    R = [set(S) for S in sets]
    choices = [[None] + [i for i in range(n) if g in R[i]] for g in range(m)]
    allP = []
    for bm in itertools.product(*choices):
        B = [frozenset(g for g in range(m) if bm[g] == i) for i in range(n)]
        if any(len(b) > 2 for b in B): continue
        J = frozenset(g for g in range(m) if bm[g] is None)
        N = [frozenset(g for g in R[i] - B[i] if vl[i][g] > val(vl[i], B[i])) for i in range(n)]
        NA = frozenset().union(*N)
        if J & NA: continue
        if any(len(B[i]) >= 2 and B[i] & NA for i in range(n)): continue
        fz = [len(B[i]) == 1 and B[i] <= NA for i in range(n)]
        allP.append((tuple(B), J, N, NA, fz))
    f = min(sum(p[4]) for p in allP)
    omega = f - (2 * n - m)
    if f == 0 or omega < 1: return None
    states = []
    for B, J, N, NA, fz in allP:
        if sum(fz) != f: continue
        cap = [0 if fz[i] else max(0, 2 - len(B[i])) for i in range(n)]
        d = CX.rodef(n, vl, B, J, fz, cap, R, N)
        key = tuple(next(iter(B[i])) if fz[i] else None for i in range(n))
        states.append((B, J, N, NA, fz, d, key))
    dstar = {}
    for s in states: dstar[s[6]] = min(dstar.get(s[6], 1 << 30), s[5])
    nb = {e: collections.defaultdict(set) for e in EDGESETS}
    for s in states:
        B, J, N, NA, fz, d, k = s
        for t in states:
            B2, J2, N2, NA2, fz2, d2, k2 = t
            if k2 == k or NA2 != NA: continue
            ch = [i for i in range(n) if B[i] != B2[i]]
            if all(fz[i] and fz2[i] for i in ch):
                nb['T3T4'][k].add(k2); nb['T3+T4'][k].add(k2); continue
            xs = [i for i in ch if fz[i] and not fz2[i]]
            zs = [i for i in ch if fz2[i] and not fz[i]]
            ws = [i for i in ch if fz[i] and fz2[i]]
            ys = [i for i in ch if not fz[i] and not fz2[i]]
            if len(xs) != 1 or len(zs) != 1 or len(ys) > 1: continue
            x, z = xs[0], zs[0]
            if not all(B[y] - B2[y] for y in ys): continue
            if sorted(map(sorted, [B2[w] for w in ws + [z]])) != sorted(map(sorted, [B[w] for w in ws + [x]])): continue
            if not B2[z] <= N[z]: continue
            nb['T3+'][k].add(k2); nb['T3+T4'][k].add(k2)
            if not ws:
                nb['T3'][k].add(k2); nb['T3T4'][k].add(k2)
    out = {}
    for k, ds in dstar.items():
        rec = {'def*': ds}
        if ds > 0:
            for e in EDGESETS:
                rec['DLK_' + e] = any(dstar[k2] < ds for k2 in nb[e][k])
                rec['nb_' + e] = sorted((','.join('-' if g is None else str(g) for g in k2), dstar[k2]) for k2 in nb[e][k])
        out[','.join('-' if g is None else str(g) for g in k)] = rec
    return f, out


def compare(recs_mine, recs_other):
    """recs_other: list of sx_keygraph per-key records"""
    bad = 0
    for r in recs_other:
        mine = recs_mine.get(r['key'])
        if mine is None or mine['def*'] != r['def*']: bad += 1; continue
        if r['def*'] > 0:
            for e in EDGESETS:
                if mine['DLK_' + e] != r['DLK_' + e] or mine['nb_' + e] != [tuple(t) for t in r['nb_' + e]]: bad += 1
    if len(recs_mine) != len(recs_other): bad += 1
    return bad


def main(argv):
    opt = dict(a[2:].split('=', 1) for a in argv if a.startswith('--') and '=' in a)
    rest = [a for a in argv if not a.startswith('--')]
    print('# command: python3 k4/sx_xcheck.py ' + ' '.join(argv), flush=True)
    cnt = collections.Counter()
    if rest[0] == 'catalog':
        import sx_keygraph as SK
        recs = json.load(gzip.open(rest[1], 'rt'))['records']
        recs = [r for r in recs if r.get('f', 1) >= 1][::int(opt.get('every', 1))]
        if 'max' in opt: recs = recs[:int(opt['max'])]
        for r in recs:
            sets, vals, m = r['core']['sets'], r['vals'], r['core']['m']
            res = keygraph(sets, vals, m)
            other = SK.run_one({'sets': sets, 'vals': vals, 'm': m})
            cnt['profiles'] += 1
            if (res is None) != (other is None): cnt['MISMATCH (scope)'] += 1; continue
            if res is None: continue
            f, mine = res
            b = compare(mine, other[1])
            cnt['keys'] += len(mine); cnt['keys def*>0'] += sum(1 for v in mine.values() if v['def*'] > 0)
            cnt['MISMATCH'] += b
            for v in mine.values():
                if v['def*'] > 0:
                    for e in EDGESETS: cnt['DLK_%s fails' % e] += not v['DLK_' + e]
    else:
        for fn in rest:
            for i, line in enumerate(gzip.open(fn, 'rt')):
                if i % int(opt.get('every', 1)): continue
                r = json.loads(line)
                if r['m'] > int(opt.get('mmax', 99)): cnt['skipped (m > mmax)'] += 1; continue
                if 'keys' not in r:                  # a sx_hunt.py dump: compare with sx_keygraph.run_one
                    import sx_keygraph as SK
                    r['keys'] = SK.run_one({'sets': r['sets'], 'vals': r['vals'], 'm': r['m']})[1]
                res = keygraph(r['sets'], r['vals'], r['m'])
                cnt['profiles'] += 1
                if res is None: cnt['MISMATCH (scope)'] += 1; continue
                f, mine = res
                b = compare(mine, r['keys'])
                cnt['keys'] += len(mine); cnt['keys def*>0'] += sum(1 for v in mine.values() if v['def*'] > 0)
                cnt['MISMATCH'] += b
                if b: print('MISMATCH', r['src'])
                for v in mine.values():
                    if v['def*'] > 0:
                        for e in EDGESETS: cnt['DLK_%s fails' % e] += not v['DLK_' + e]
    for k in sorted(cnt): print('%-30s %d' % (k, cnt[k]))


if __name__ == '__main__':
    main(sys.argv[1:])
