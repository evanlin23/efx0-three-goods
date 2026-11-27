"""Lemma DEMOTE candidate (k4/girth.md section 7): at an OC1^max failure with receiver u, the receiver-first picks Y'
differ from the failing picks Y only along the RF path u -> x1 -> ... -> d (d = the last agent, which takes a junk
good or u's old pick and loses value).  Which completion with owner d works?

Per failing order (n = 4: all 292,080 or every STRIDE-th; n = 5: the 24 stored failures, all orders), with J' the junk
at Y' (main's raw EFX0, k4/sdc/oc1_mc2_rand.Inst.efx0):
  ALL    Y' plus every junk good to d;
  ALL-1  Y' plus every junk good to d except one, which goes to one other agent (some choice);
  OWNER  some one-absorber completion with owner d (d takes >= 2 junk goods, every other agent at most one);
  ANY    some one-absorber completion at Y' (any owner, or none);
and the roles at Y' (|U'|, |D'|, |D_T'|), for the classification by proved OC1 classes.  For the orders where no
completion exists at Y', the official move (Inst.moves) that repairs is classified (addition / chain / ring, who moves).
EVIDENCE.

    python3 k4/girth/oc1_demote.py [STRIDE]
"""
import collections
import gzip
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, 'k4', 'sdc'))
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_rf_owner import owner_ok  # noqa: E402


def rf_path(Y, Y2, J, u):
    path, cur = [u], u
    while True:
        g = Y2[cur]
        if g in J:
            return path, 'junk'
        nxt = Y.index(g)
        if nxt in path:
            return path, 'pick of %s' % ('u' if nxt == u else 'path')
        path.append(nxt)
        cur = nxt


def describe_move(base, st, rl2, J2, path):
    """a repairing move state st against the bases: per changed agent, its role at Y' (with its place on the RF path)
    and what its new bundle holds: its own pick, another agent's pick (by that agent's role), junk goods"""
    n = len(base)
    holder = {b[0]: i for i, b in enumerate(base) if b}
    tag = {path[0]: '(u)', path[-1]: '(d)'}
    if len(path) == 3:
        tag[path[1]] = '(w)'
    parts = []
    for i in range(n):
        if sorted(st[i]) == sorted(base[i]):
            continue
        got = []
        for g in sorted(st[i]):
            if g in J2:
                got.append('junk')
            elif holder.get(g) == i:
                got.append('own pick')
            else:
                got.append('pick of ' + rl2[holder[g]] + tag.get(holder[g], ''))
        parts.append('%s%s takes {%s}' % (rl2[i], tag.get(i, ''), ', '.join(got)))
    return '; '.join(sorted(parts))


def analyse(sets, vals, Y, o, C, tag, full):
    n = len(sets)
    R = [set(S) for S in sets]
    v = [dict(zip(sets[i], vals[i])) for i in range(n)]
    rl, J = roles(sets, vals, list(Y))
    u = rl.index('U')
    Y2 = sd(R, v, [u] + [a for a in o if a != u])
    nu = len([p for p in Y2 if p is not None])
    if nu < n:
        C[(tag, 'RF picks not perfect')] += 1
        return
    path, end = rf_path(Y, Y2, J, u)
    d = path[-1]
    changed = {i for i in range(n) if Y2[i] != Y[i]}
    C[(tag, 'orders')] += 1
    C[(tag, 'only the path changes')] += changed == set(path)
    C[(tag, 'd ends with ' + end)] += 1
    C[(tag, 'd loses value')] += v[d].get(Y2[d], 0) < v[d][Y[d]]
    C[(tag, 'path roles ' + '->'.join(rl[i] for i in path))] += 1
    rl2, J2 = roles(sets, vals, list(Y2))
    C[(tag, "at Y': |U'| = %d" % rl2.count('U'))] += 1
    C[(tag, "at Y': |D_T'| = %d" % rl2.count('DT'))] += 1
    C[(tag, "at Y': d is %s" % rl2[d])] += 1
    nu_, ndt = rl2.count('U'), rl2.count('DT')
    if nu_ >= 2:
        cls = "class R2 (|U'| >= 2; certified at n = 4, K4.SDC.R2.N4)"
    elif ndt == 1:
        cls = "class U1 (|U'| = 1, |D_T'| = 1; Corollary U1, K4.MULTI.U)"
    else:
        cls = "residue (|U'| = 1, |D_T'| = %d)" % ndt
    C[(tag, cls)] += 1
    if full:
        C[(tag, 'sampled: ' + cls)] += 1
    I = Inst(sets, vals)
    base = [[p] for p in Y2]
    J2 = sorted(J2)
    B = [list(b) for b in base]
    B[d] += J2
    allok = I.efx0(B)
    C[(tag, 'ALL: every junk good to d is EFX0')] += allok
    if not full:
        return
    all1 = allok
    if not allok:
        for g in J2:
            for i in range(n):
                if i == d:
                    continue
                B = [list(b) for b in base]
                B[d] += [h for h in J2 if h != g]
                B[i].append(g)
                if I.efx0(B):
                    all1 = True
                    break
            if all1:
                break
    C[(tag, 'ALL or ALL-1 (one junk good to another agent)')] += all1
    own = owner_ok(I, base, d) if len(J2) >= 2 else False
    w = path[1]
    ownw = owner_ok(I, base, w) if len(J2) >= 2 else False
    C[(tag, 'OWNER w (holder of the receiver top good) works')] += ownw
    C[(tag, 'OWNER d or w works')] += own or ownw
    anyc = own or ownw or any(owner_ok(I, base, a) for a in [None] + [i for i in range(n) if i not in (d, w)])
    C[(tag, 'OWNER d: some one-absorber completion with owner d')] += own
    C[(tag, 'ANY: some one-absorber completion at the picks')] += anyc
    C[(tag, 'sampled: %s, %s' % (cls, 'completes at the picks' if anyc else 'needs a move'))] += 1
    if not anyc:
        kinds = set()
        for stt in I.moves(base):
            st = [list(b) for b in stt]
            if I.one_absorber(st):
                kinds.add(describe_move(base, st, rl2, J2, path))
        C[(tag, 'needs a move')] += 1
        C[(tag, 'needs a move, repairing moves available: %d' % min(len(kinds), 5))] += 1
        for k in kinds:
            C[(tag, 'repairing move: ' + k)] += 1


def main():
    stride = int(sys.argv[1]) if len(sys.argv) > 1 else 97
    print('$ python3 k4/girth/oc1_demote.py', *sys.argv[1:], flush=True)
    C = collections.Counter()
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    k = 0
    for h in d['hypergraphs']:
        sets = h['sets']
        R = [set(S) for S in sets]
        for st in h['starts']:
            v = [dict(zip(sets[i], st['vals'][i])) for i in range(len(sets))]
            Y = tuple(st['picks'])
            for o in itertools.permutations(range(len(sets))):
                if sd(R, v, o) != Y:
                    continue
                k += 1
                analyse(sets, st['vals'], Y, o, C, 'n=4', k % stride == 0)
    for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl')):
        r = json.loads(line)
        R = [set(S) for S in r['sets']]
        v = [dict(zip(r['sets'][i], r['vals'][i])) for i in range(len(r['sets']))]
        Y = tuple(r['picks'])
        for o in itertools.permutations(range(len(r['sets']))):
            if sd(R, v, o) == Y:
                analyse(r['sets'], r['vals'], Y, o, C, 'n=5', True)
    for tag in ('n=4', 'n=5'):
        for key in sorted(k2 for t, k2 in C if t == tag):
            print('%s  %-72s %7d' % (tag, key, C[(tag, key)]))
    print('(n = 4: the ALL, path and role counts are over every failing order; ALL-1, OWNER, ANY and the moves over '
          'every %d-th)' % stride)
    sys.stdout.flush()


if __name__ == '__main__':
    main()
