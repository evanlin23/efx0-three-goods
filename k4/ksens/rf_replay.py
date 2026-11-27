"""Conjecture RF (receiver first; k4/sdc.md §31 end, on main) replayed on this workstream's OC1^max failures at k = 5
(k4/ksens.md §8): the 13 n = 3 witnesses of kcegar (kcegar_k5_n3_D1.log, N3K5 among them), RD5 and PW5.

For each failing maximum-matching start Y (picks of an order, one-absorber OC1 failing under the official move rule):
- receivers of Y: agents u with a pick such that no other agent values u's pick above its own pick;
- for each receiver u, every order with u first whose picks are a maximum matching; RF says each satisfies OC1.
Everything by brute force from the definitions (brute.py: SD picks, every chain under the official rule, raw-EFX0
backtracking completions with at most one absorber).

    python3 k4/ksens/rf_replay.py"""
import json, itertools, time
import _paths
import brute
from maxmatch import nu


def oc1(I, Y, n):
    base = [frozenset([g]) if g is not None else frozenset() for g in Y]
    if I.completes(base, 1): return 'picks'
    for s in I.chains(base, empty_pass=False):
        if I.completes([frozenset(x) for x in s], 1): return 'one chain'
    return None


def replay(name, sets, vals):
    n = len(sets); m = 1 + max(max(s) for s in sets); I = brute.Inst(sets, vals, m); v = nu(sets, vals)
    val = lambda i, g: dict(zip(sets[i], vals[i])).get(g, 0)
    starts = {}
    for o in itertools.permutations(range(n)):
        Y = tuple(I.sd(o)); starts.setdefault(Y, []).append(o)
    out = []
    for Y, orders in sorted(starts.items(), key=lambda t: str(t[0])):
        if sum(g is not None for g in Y) != v or oc1(I, Y, n): continue
        rec = [u for u in range(n) if Y[u] is not None and
               not any(j != u and val(j, Y[u]) > (val(j, Y[j]) if Y[j] is not None else 0) for j in range(n))]
        res = {}
        for u in rec:
            ys = {}
            for o in itertools.permutations(range(n)):
                if o[0] != u: continue
                Z = tuple(I.sd(o))
                if sum(g is not None for g in Z) == v: ys[Z] = oc1(I, Z, n)
            res[u] = ys
        ok = bool(rec) and all(ys and all(r is not None for r in ys.values()) for ys in res.values())
        out.append((Y, rec, res, ok))
        print('%s: failing start %s (orders %s); receivers %s; u-first maximum-matching pick vectors and OC1: %s; RF %s' % (
            name, Y, orders[:3], rec, {u: {str(z): r for z, r in ys.items()} for u, ys in res.items()},
            'holds' if ok else 'FAILS'), flush=True)
    return out


if __name__ == '__main__':
    print('$ python3 k4/ksens/rf_replay.py', flush=True); t0 = time.time(); tot = bad = 0
    cases = []
    for l in open('../../results/k4_ksens/kcegar_k5_n3_D1.log'):
        if '"result": "FAIL"' in l:
            r = json.loads(l); cases.append((r['name'], r['sets'], r['recheck']['vals']))
    import refute_rd_k5 as RD, fam_ladder
    cases.append(('RD5', RD.SETS, RD.VALS))
    s, v_, m = fam_ladder.clean(3, 2, 4); cases.append(('PW5', s, v_))
    for name, S, V in cases:
        for Y, rec, res, ok in replay(name, S, V): tot += 1; bad += not ok
    print('failing maximum-matching starts: %d; RF fails on %d (%.0f s)' % (tot, bad, time.time() - t0))
