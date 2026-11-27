"""The two residue lemmas of the DEMOTE decomposition of Rule RF (k4/girth.md section 7), checked on EVERY failing
order (n = 4: all 292,080 of results/k4_oc1max/two_move_starts_n4.json.gz; n = 5: all 86 of the 24 stored failures).

Setting.  Y = an OC1^max failure with receiver u, o an order giving Y, Y' = the picks of (u, o - u), P = (u = x0,
x1 = w, ..., x_l = d) the RF path (w holds u's top good at Y; d is the last agent).  Roles at Y' as in
k4/girth/oc1_cycles.py: U' receivers, D' dangerous, D_T' truly dangerous, J' junk.

Unified statement (as run; check_one): (i) w or d owns a one-absorber completion at Y'; else (T) a receiver r of Y'
(d first) and a pick-dangerous agent p trade, p adding one junk good: "p takes {Y'_r, j}, r takes {Y'_p}"; else (C) the
chain below (C: head d; C': any other head h, needed at the n = 5 starts with two receivers, k4/girth/oc1_r2n5.py).
The residue lemmas are its restrictions:

Lemma DEMOTE-0 (|U'| = 1, D_T' empty).  (i) Y' has a one-absorber completion whose owner is w or d, or (ii) for some
pick-dangerous agent p and junk good j of J' valued by p, the 2-ring "p takes {Y'_d, j}, d takes {Y'_p}" (both
improve, so it is an official ring) gives a state with a one-absorber completion (any owner).

Lemma DEMOTE-2 (|U'| = 1, |D_T'| = 2).  (i) as above, or (ii) for some truly dangerous agent k and some improving set
H of junk goods of J' that k values, the chain "k takes H, d takes Y'_k plus a set H_d of junk goods" (d improves; an
official chain with head d) gives a state with a one-absorber completion (any owner).

The moves of (ii) are built here from the statement and then confirmed to be official moves of main's raw checker
(k4/sdc/oc1_mc2_rand.Inst.moves); completions are Inst.one_absorber and, for (i), the owner-split enumeration of
k4/girth/oc1_rf_owner.owner_ok (raw EFX0).  The classes R2 (|U'| >= 2) and U1 (|U'| = 1, |D_T'| = 1) are counted, and
(i) is also tested there.  Repeated (profile, Y') pairs are checked once.

    python3 k4/girth/oc1_residue.py [JOBS]
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
from oc1_mc2_rand import Inst  # noqa: E402
from oc1_cycles import roles  # noqa: E402
from oc1_recvfirst import sd  # noqa: E402
from oc1_rf_owner import owner_ok  # noqa: E402
from oc1_demote import rf_path  # noqa: E402


def subsets(xs, kmin=0):
    for r in range(kmin, len(xs) + 1):
        yield from itertools.combinations(xs, r)


def key(st):
    return tuple(tuple(sorted(b)) for b in st)


def check_one(sets, vals, Y2, w, d):
    """returns (class, verdict) for the RF picks Y2 with path agents w, d.  Unified statement DEMOTE: (i) w or d owns a
    one-absorber completion; else (T) a receiver r and a pick-dangerous agent p trade, p adding one junk good; else (C)
    a truly dangerous agent k takes an improving junk set and d takes Y'_k (plus junk).  Every move tried is confirmed
    to be an official move of Inst.moves."""
    n = len(sets)
    I = Inst(sets, vals)
    v = I.v
    rl2, J2 = roles(sets, vals, list(Y2))
    J2 = sorted(J2)
    nU, nDT = rl2.count('U'), rl2.count('DT')
    cls = 'R2' if nU >= 2 else ('U1' if nDT == 1 else 'residue D_T\'=%d' % nDT)
    base = [[p] for p in Y2]
    if len(J2) >= 2 and (owner_ok(I, base, w) or owner_ok(I, base, d)):
        return cls, '(i) w or d owns'
    official = [None]

    def is_official(st):
        if official[0] is None:
            official[0] = {key(s_) for s_ in I.moves(base)}
        return key(st) in official[0]

    tried = 0
    # (T) a receiver r trades with a pick-dangerous agent p, who adds one junk good
    for r in sorted(range(n), key=lambda a: a != d):
        if rl2[r] != 'U':
            continue
        for p in range(n):
            if rl2[p] != 'Dp':
                continue
            for j in J2:
                if j not in v[p]:
                    continue
                if not (I.V(p, [Y2[r], j]) > I.V(p, [Y2[p]]) and I.V(r, [Y2[p]]) > I.V(r, [Y2[r]])):
                    continue
                st = [list(b) for b in base]
                st[p] = [Y2[r], j]
                st[r] = [Y2[p]]
                tried += 1
                assert is_official(st), 'the trade is not an official move'
                if I.one_absorber(st):
                    return cls, '(T) %s trades with a pick-dangerous agent' % ('d' if r == d else 'another receiver')
    # (T*) a ring of length 3 through a receiver r: c1 (pick-dangerous) takes {Y'_r, j}, c2 takes Y'_{c1}, r takes
    # Y'_{c2}; everyone improves (an official ring).  Needed at 32 n = 5 DEMOTE-0 starts on 5_pure#374.
    for r in sorted(range(n), key=lambda a: a != d):
        if rl2[r] != 'U':
            continue
        for c1 in range(n):
            if c1 == r or rl2[c1] != 'Dp':
                continue
            for c2 in range(n):
                if c2 in (r, c1):
                    continue
                for j in J2:
                    if j not in v[c1]:
                        continue
                    if not (I.V(c1, [Y2[r], j]) > I.V(c1, [Y2[c1]]) and I.V(c2, [Y2[c1]]) > I.V(c2, [Y2[c2]])
                            and I.V(r, [Y2[c2]]) > I.V(r, [Y2[r]])):
                        continue
                    st = [list(b) for b in base]
                    st[c1] = [Y2[r], j]
                    st[c2] = [Y2[c1]]
                    st[r] = [Y2[c2]]
                    tried += 1
                    assert is_official(st), 'the 3-ring is not an official move'
                    if I.one_absorber(st):
                        return cls, "(T*) a 3-ring through %s, a pick-dangerous agent adding a junk good" % (
                            'd' if r == d else 'another receiver')
    # (C) a truly dangerous agent k takes an improving junk set H, a head h takes Y'_k plus junk (h improves): first
    # with h = d (the form found at n = 4), then any other head (needed at the n = 5 starts with two receivers)
    for head_is_d in (True, False):
        for k in range(n):
            if rl2[k] != 'DT':
                continue
            for H in subsets([g for g in J2 if g in v[k]], 1):
                if not I.V(k, H) > I.V(k, [Y2[k]]):
                    continue
                for h in ([d] if head_is_d else [x for x in range(n) if x not in (k, d)]):
                    if h == k:
                        continue
                    rest = [g for g in J2 if g not in H and g in v[h]]
                    for Hd in subsets(rest):
                        if not I.V(h, [Y2[k]] + list(Hd)) > I.V(h, [Y2[h]]):
                            continue
                        st = [list(b) for b in base]
                        st[k] = list(H)
                        st[h] = [Y2[k]] + list(Hd)
                        tried += 1
                        assert is_official(st), 'the chain is not an official move'
                        if I.one_absorber(st):
                            return cls, ('(C) the chain k -> d' if head_is_d else
                                         "(C') the chain k -> h, h a %s other than d" % rl2[h])
    return cls, 'FAILS (%d moves of the statement tried)' % tried


def job(task):
    sets, starts = task
    n = len(sets)
    R = [set(S) for S in sets]
    out = collections.Counter()
    fails = []
    seen = {}
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
            out['orders'] += 1
            if None in Y2:
                out['RF picks not perfect'] += 1
                continue
            path, end = rf_path(Y, Y2, J, u)
            w, d = path[1], path[-1]
            kk = (tuple(map(tuple, vals)), Y2, w, d)
            if kk not in seen:
                seen[kk] = check_one(sets, vals, Y2, w, d)
                out['distinct (profile, RF picks, w, d)'] += 1
            cls, verdict = seen[kk]
            out[(cls, verdict)] += 1
            if verdict.startswith('FAILS') and len(fails) < 3:
                fails.append((sets, vals, list(Y), list(o), list(Y2)))
    return out, fails


def main():
    jobs = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    print('$ python3 k4/girth/oc1_residue.py', *sys.argv[1:], flush=True)
    t0 = time.time()
    d = json.load(gzip.open(os.path.join(ROOT, 'results/k4_oc1max/two_move_starts_n4.json.gz')))
    tasks = []
    for h in d['hypergraphs']:
        for i in range(0, len(h['starts']), 400):
            tasks.append((h['sets'], h['starts'][i:i + 400]))
    n5 = [json.loads(line) for line in open(os.path.join(ROOT, 'results/k4_oc1max/oc1prime_cex_n5_partial.jsonl'))]
    tasks5 = [(r['sets'], [{'vals': r['vals'], 'picks': r['picks']}]) for r in n5]
    for tag, T in (('n = 4 (all failing orders)', tasks), ('n = 5 (the 24 stored failures)', tasks5)):
        C = collections.Counter()
        F = []
        with mp.Pool(jobs) as pool:
            for k, (c, f) in enumerate(pool.imap_unordered(job, T)):
                C.update(c)
                F += f
                if (k + 1) % 50 == 0:
                    print('  ... %d of %d chunks, %.0f s' % (k + 1, len(T), time.time() - t0), flush=True)
        print(tag + ':')
        for kk in sorted(C, key=str):
            print('   %-70s %8d' % (' / '.join(kk) if isinstance(kk, tuple) else kk, C[kk]))
        for f in F[:3]:
            print('   FAILING CASE', f)
    print('time %.0f s' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
