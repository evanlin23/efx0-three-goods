"""Screening of DE-style state spaces at k = 4 (attempts/k4-de4-ss.md; ledger K4.DE4.SS, K4.DE4V3). EVIDENCE only.

  python3 k4/de4/ss_screen.py      every variant below on every instance of the screen set; prints, per variant, the
                                   instances where some maximum (every-fail) or every maximum (no completable
                                   maximum) has no EFX0 completion

A variant: which multi-good holdings are allowed (beyond the empty set and single goods), their levels, and extra
validity rules. Valid: (V1) wanted goods are single holdings, (V2) no holding threatens another agent, plus extras.
Maxima: largest level sum, then value-Pareto. Claim tested: every maximum has an EFX0 completion."""
import sys, json, glob, random, itertools, collections, multiprocessing as mp
import os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
from de4lib import Inst, subsets, EFXSearch, bundles

def types(I, i, A):
    """the type of holding A for agent i (None if not one of the named types)"""
    r = I.ranked(i); v = I.v[i]; S = set(A)
    if not S <= set(r):
        return None
    if len(S) == 0: return 'E'
    if len(S) == 1: return 'abcd'[r.index(A[0])]
    top = v[r[0]]; val = sum(v[g] for g in S)
    if val > top and all(val - v[h] <= top for h in S):
        return 'U'
    if len(r) == 4:
        a, b, c, d = r
        if S == {c, d}:
            return 'LP' if v[b] < val < top else ('CD' if val < v[b] else None)
        if S == {b, c} and val < top: return 'BC'
        if S == {b, d} and val < top: return 'BD'
    return None

BASE_LEV = {'E': 0, 'a': 4, 'b': 3, 'c': 2, 'd': 1, 'U': 5}

class Variant:
    def __init__(self, name, lev, extra=()):
        self.name = name
        self.lev = dict(BASE_LEV); self.lev.update(lev)    # allowed multi types = keys of lev besides U
        self.extra = set(extra)
    def allowed(self, I, i, A):
        t = types(I, i, A)
        return t is not None and t in self.lev
    def level(self, I, i, A):
        return self.lev[types(I, i, A)]

def wanted(I, i, A):
    vA = I.val(i, A)
    return [g for g in I.sets[i] if g not in A and I.v[i][g] > vA]

def valid(V, I, Y):
    alone = set(A[0] for A in Y if len(A) == 1)
    W = set()
    for i in range(I.n):
        W |= set(wanted(I, i, Y[i]))
    if not W <= alone:
        return False
    for j in range(I.n):
        if len(Y[j]) < 2: continue
        for i in range(I.n):
            if i != j and I.theta(i, Y[j]) > I.val(i, Y[i]):
                return False
    if 'v3' in V.extra or 'v3f' in V.extra:   # a lower-pair holder's b is held (v3f: held alone by a frozen agent)
        held = set(g for A in Y for g in A)
        for i in range(I.n):
            if types(I, i, Y[i]) == 'LP':
                b = I.ranked(i)[1]
                if b not in held: return False
                if 'v3f' in V.extra and (b,) not in [tuple(A) for A in Y]: return False
    return True

def all_states(V, I):
    opts = [[A for A in subsets(I.sets[i]) if V.allowed(I, i, A)] for i in range(I.n)]
    res = []
    def rec(i, used, Y):
        if i == I.n:
            if valid(V, I, Y): res.append(list(Y))
            return
        for A in opts[i]:
            if used.isdisjoint(A):
                Y.append(A); rec(i + 1, used | set(A), Y); Y.pop()
    rec(0, set(), [])
    return res

def maxima(V, I, S):
    if not S: return []
    pot = lambda Y: sum(V.level(I, i, Y[i]) for i in range(I.n))
    best = max(map(pot, S))
    top = [Y for Y in S if pot(Y) == best]
    vals = [tuple(I.val(i, Y[i]) for i in range(I.n)) for Y in top]
    return [top[k] for k in range(len(top)) if not any(all(a >= b for a, b in zip(vals[l], vals[k])) and vals[l] != vals[k] for l in range(len(top)))]

class Comp:
    def __init__(self, I):
        self.I = I; self.S = EFXSearch(I); self.cache = {}
    def ok(self, Y):
        key = tuple(map(tuple, Y))
        if key not in self.cache:
            units = [[self.S.x[g][j]] for j, A in enumerate(Y) for g in A]
            self.cache[key] = self.S.solve(units) is not None
        return self.cache[key]

def screen(V, I, C=None):
    C = C or Comp(I)
    S = all_states(V, I)
    mx = maxima(V, I, S)
    bad = [Y for Y in mx if not C.ok(Y)]
    return (not bad), len(mx), bad[:1], any(C.ok(Y) for Y in mx)

def inst_from_dicts(ds):
    sets = [sorted(d) for d in ds]
    return Inst(sets, [[d[g] for g in s] for s, d in zip(sets, ds)], 1 + max(max(d) for d in ds))

def screen_set():
    out = []
    out.append(('A131', Inst([[0,2,4,6],[1,3,5,6],[2,3,6],[4,5,6]], [[3,8,2,4],[3,2,8,4],[4,2,3],[2,4,3]], 7)))
    out.append(('B131', Inst([[0,2,4,6],[1,3,5,6],[2,3,6],[4,5,6]], [[3,2,8,4],[3,8,2,4],[2,4,3],[4,2,3]], 7)))
    out.append(('C127', Inst([[0,2,3,5],[1,4,6],[2,3,5,6],[4,5,6]], [[2,8,5,4],[2,4,3],[4,2,3,8],[4,2,3]], 7)))
    out.append(('D3', Inst([[0,1,2,4],[1,2,3,5],[2,3,4,5]], [[4,8,3,2],[8,4,3,2],[10,7,2,4]], 6)))
    import gm4_counterexample as G
    for name, ds, Y, kind in G.INSTANCES:
        out.append(('GM4-' + name.split(':')[0], inst_from_dicts(ds)))
    for f in sorted(glob.glob(os.path.join(ROOT, 'k4/suite/instances/*.json'))):
        d = json.load(open(f))
        if d['n'] <= 5 and d['m'] <= 11 and d.get('vals'):
            try:
                out.append((d['id'], Inst.from_json(d)))
            except Exception:
                pass
    return out


V = Variant
VARIANTS = [
    V('DE4', {'LP': 3}),
    V('DE4+v3', {'LP': 3}, ['v3']),
    V('DE4+v3f', {'LP': 3}, ['v3f']),
    V('LP2.5', {'LP': 2.5}),
    V('LP2.5+v3', {'LP': 2.5}, ['v3']),
    V('noLP', {}),
    V('BCBD3.5', {'BC': 3.5, 'BD': 3.5}),
    V('LP3+BCBD3.5', {'LP': 3, 'BC': 3.5, 'BD': 3.5}),
    V('LP3+v3+BCBD3.5', {'LP': 3, 'BC': 3.5, 'BD': 3.5}, ['v3']),
    V('LP3.5', {'LP': 3.5}),
    V('LP3+CD2.5', {'LP': 3, 'CD': 2.5}),
    V('LP3+v3+CD2.5', {'LP': 3, 'CD': 2.5}, ['v3']),
]
def job(k):
    name, I = SET[k]
    C = Comp(I)
    out = []
    for Vr in VARIANTS:
        ok, nmx, bad, some = screen(Vr, I, C)
        out.append((Vr.name, ok, some, bad))
    return name, out
SET = screen_set()
if __name__ == '__main__':
    fails = collections.defaultdict(list); somef = collections.defaultdict(list)
    with mp.Pool(4) as p:
        for name, out in p.imap_unordered(job, range(len(SET))):
            for vn, ok, some, bad in out:
                if not ok: fails[vn].append(name)
                if not some: somef[vn].append(name)
    for Vr in VARIANTS:
        print('%-18s every-fail %3d %s | no completable maximum %d %s' % (Vr.name, len(fails[Vr.name]), fails[Vr.name][:8], len(somef[Vr.name]), somef[Vr.name][:5]))
