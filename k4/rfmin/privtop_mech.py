"""Mechanism of the lift test (k4/RFMIN.md §6): at the lifted starts (receiver u's private pick raised to its top), let
t be u's old top and x1 its holder (Y_x1 = t). Checks: (i) before the lift u wants t; (ii) who else wants t (if nobody,
x1 is unfrozen after the lift); (iii) whether the lifted picks have a one-absorber completion in which x1 takes junk,
and one in which x1 takes none; (iv) whether the unlifted picks have a completion at all (they must not: OC1 fails).
Modes: x1 (default; the checks above), threats (every lifted completion read in the original values: which bundle
threatens u), owner (is there a lifted completion with absorber u).
Usage: privtop_mech.py FILE.json.gz STRIDE [x1|threats|owner]"""
import sys, os, gzip, json, collections, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'sdc'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from oc1_mc2_rand import Inst
from privtop_lift import lift
from multiprocessing import Pool

def completions(I, base, x1_junk):
    """Is there a one-absorber EFX0 completion of base with x1 receiving junk (x1_junk True) / none (False)?"""
    n = I.n; J = [g for g in range(I.m) if all(g not in b for b in base)]
    for a in [None] + list(range(n)):
        for r in range(0 if a is None else 2, len(J) + 1):
            if a is None and r: break
            for S in itertools.combinations(J, r):
                rest = [g for g in J if g not in S]; others = [i for i in range(n) if i != a]
                for recv in itertools.permutations(others, len(rest)):
                    gets = (a == X1 and r > 0) or (X1 in recv)
                    if gets != x1_junk: continue
                    B = [list(b) for b in base]
                    if a is not None: B[a] += list(S)
                    for g, i in zip(rest, recv): B[i].append(g)
                    if I.efx0(B): return True
    return False

X1 = None
def job(args):
    global X1
    sets, starts = args
    C = collections.Counter()
    for s in starts:
        Y = s['picks']; n = len(sets)
        deg = collections.Counter(g for S in sets for g in S)
        for u in s['receivers']:
            p = Y[u]
            if p is None or deg[p] != 1: continue
            vals = [list(v) for v in s['vals']]
            v0 = dict(zip(sets[u], vals[u]))
            t = max(v0, key=v0.get)
            x1 = next(a for a in range(n) if Y[a] == t)
            X1 = x1
            I0 = Inst(sets, vals)
            others = [i for i in range(n) if i != x1 and i != u and I0.v[i].get(t, 0) > (I0.v[i].get(Y[i], 0) if Y[i] is not None else 0)]
            C['u wants t before the lift'] += I0.v[u][t] > I0.v[u][p]
            C['t also wanted by another agent' if others else 'only u wants t (x1 unfrozen after the lift)'] += 1
            k = sets[u].index(p); y = lift(vals[u], k); vals[u] = y
            I1 = Inst(sets, vals)
            base = [[g] if g is not None else [] for g in Y]
            a = completions(I1, base, True); b = completions(I1, base, False)
            C['lifted: completion with x1 taking junk %s, without %s' % (a, b)] += 1
    return C

def main():
    path, stride = sys.argv[1], int(sys.argv[2])
    mode = sys.argv[3] if len(sys.argv) > 3 else 'x1'
    fn = {'x1': job, 'threats': job2, 'owner': job3}[mode]
    T = collections.Counter()
    with Pool(4) as pool:
        for C in pool.imap_unordered(fn, tasks_of(path, stride, 20)): T.update(C)
    print(path, 'stride', stride, 'mode', mode)
    for k, x in sorted(T.items()): print('  %-70s %d' % (k, x))




def first_completion(I, base):
    n = I.n; J = [g for g in range(I.m) if all(g not in b for b in base)]
    for a in [None] + list(range(n)):
        for r in range(0 if a is None else 2, len(J) + 1):
            if a is None and r: break
            for S in itertools.combinations(J, r):
                rest = [g for g in J if g not in S]; others = [i for i in range(n) if i != a]
                for recv in itertools.permutations(others, len(rest)):
                    B = [list(b) for b in base]
                    if a is not None: B[a] += list(S)
                    for g, i in zip(rest, recv): B[i].append(g)
                    if I.efx0(B): yield a, B


def job2(args):
    """Every lifted completion, read in the original values: which bundle threatens u, and which of u's goods it holds."""
    sets, starts = args
    C = collections.Counter()
    for s in starts:
        Y = s['picks']; n = len(sets)
        deg = collections.Counter(g for S in sets for g in S)
        for u in s['receivers']:
            p = Y[u]
            if p is None or deg[p] != 1: continue
            vals = [list(v) for v in s['vals']]
            I0 = Inst(sets, vals)
            v0 = I0.v[u]; t = max(v0, key=v0.get)
            above = {g for g in v0 if v0[g] > v0[p]}
            k = sets[u].index(p); y = lift(vals[u], k); vals1 = [list(v) for v in vals]; vals1[u] = y
            I1 = Inst(sets, vals1)
            base = [[g] if g is not None else [] for g in Y]
            kinds = set()
            for a, B in itertools.islice(first_completion(I1, base), 200):
                own = I0.V(u, B[u])
                thr = [j for j in range(n) if j != u and B[j] and I0.V(u, B[j]) - min(v0.get(h, 0) for h in B[j]) > own]
                assert thr, 'a lifted completion is EFX0 in the original values'
                j = thr[0]
                kinds.add('threat: %s bundle holding %s' % ('the absorber' if j == a else 'a single-junk' if len(B[j]) == 2 else 'another',
                          '+'.join(sorted(('top' if g == t else 'above-p' if g in above else 'junk-of-u' if g in v0 else 'other') for g in B[j] if g in v0))))
            for kd in kinds: C[kd] += 1
            C['starts'] += 1
    return C



def job3(args):
    """Is there a lifted completion whose absorber is u, the private-top agent after the lift?"""
    sets, starts = args
    C = collections.Counter()
    for s in starts:
        Y = s['picks']
        deg = collections.Counter(g for S in sets for g in S)
        for u in s['receivers']:
            p = Y[u]
            if p is None or deg[p] != 1: continue
            vals = [list(v) for v in s['vals']]; k = sets[u].index(p); vals[u] = lift(vals[u], k)
            I1 = Inst(sets, vals); base = [[g] if g is not None else [] for g in Y]
            owners = set(a for a, B in itertools.islice(first_completion(I1, base), 5000))
            C['completion with absorber u (the private-top agent) exists' if u in owners else 'no completion with absorber u'] += 1
    return C


def tasks_of(path, stride, chunk):
    d = json.load(gzip.open(path))
    out = []
    for H in d['hypergraphs']:
        deg = collections.Counter(g for S in H['sets'] for g in S)
        st = [s for s in H['starts'] if any(s['picks'][u] is not None and deg[s['picks'][u]] == 1 for u in s['receivers'])][::stride]
        for i in range(0, len(st), chunk): out.append((H['sets'], st[i:i + chunk]))
    return out


if __name__ == '__main__':
    main()
