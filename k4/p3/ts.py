"""Conjecture TS (k4/p3.md section 4): LB4's Phase 1 (index insertion), an upgrade policy, at most R rotations, then a
completion in which the bases are kept and at most B bundles have three or more goods.

The pre-allocation steps follow k4/lb4.md sections 1-2 and 5 (re-implemented here from the text):
  Phase 1          p3lib.phase1 (serial dictatorship; P-steps for agents that lost a good, LB's key; index insertion)
  needs            pick base {Y}: the goods ranked above Y; no base: all of R_i; other bases: value-based
                   {g in R_i - B_i : v_i(g) > v_i(B_i)}
  frozen           the base is a single good of NA = union of the needs
  upgrades         policy 1 (need-shrinking) and 2 (envy-free) of k4/lb4.md; policy 0: none
  rotation         a frozen k, a need chain k = x_0, ..., x_t (x_1..x_{t-1} frozen, Y_{x_{i-1}} in N_{x_i}, x_t not
                   frozen), every x_i takes Y_{x_{i-1}}, B_{x_t} returns to the junk, k takes a nonempty
                   O subset of R_k & (J | B_{x_t}) (value-based needs)
The completion step is not LB4's owner step: SAT decides whether some EFX0 allocation (raw definition) keeps every base
and has at most B bundles of >= 3 goods. This tests the conjecture in its weakest completion form (any such
allocation, owners chosen freely; frozen agents are not forced to hold exactly their bases, the raw check decides).
    python3 k4/p3/ts.py SRC [--R=1] [--B=2] [--n=6] [--count=100] [--seed=1]    SRC as in k4/p3/dump_rules.py, or ht
                [--t=1,2 --vars=HABC]  (ht: H_t and the H3_t variants)
"""
import sys, os, random, json, time, collections, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import *


class State:
    def __init__(self, I, base, kind):
        self.I = I; self.base = [frozenset(b) for b in base]; self.kind = list(kind)   # kind: 'pick' | 'set'

    def held(self):
        return set().union(*self.base)

    def junk(self):
        return set(range(self.I.m)) - self.held()

    def needs(self, i):
        I = self.I; B = self.base[i]
        if not B: return set(I.sets[i])
        if self.kind[i] == 'pick':
            (y,) = tuple(B); return {g for g in I.sets[i] if I.v[i][g] > I.v[i][y] or (I.v[i][g] == I.v[i][y] and g < y)}
        vb = I.val(i, B)
        return {g for g in I.sets[i] if g not in B and I.v[i][g] > vb}

    def NA(self):
        return set().union(*(self.needs(i) for i in range(self.I.n)))

    def frozen(self):
        na = self.NA()
        return [len(b) == 1 and next(iter(b)) in na for b in self.base]

    def valid(self):
        na = self.NA()
        if self.junk() & na: return False
        return all(not (len(b) >= 2 and b & na) for b in self.base)

    def key(self):
        return (tuple(self.base), tuple(self.kind))


def initial(I):
    pk, order = phase1(I)
    return State(I, [{g} if g is not None else set() for g in pk], ['pick'] * I.n), order


def upgrade(s, policy):
    if policy == 0: return s
    I = s.I; s = State(I, s.base, s.kind)
    while True:
        na = s.NA(); J = s.junk(); done = False
        for k in range(I.n):
            if s.kind[k] != 'pick' or len(s.base[k]) != 1: continue
            (y,) = tuple(s.base[k])
            Nk = s.needs(k)
            if y in na or not Nk: continue
            cands = []
            for g in I.sets[k]:
                if g not in J: continue
                if policy == 1:
                    Np = {x for x in Nk if I.v[k][x] > I.v[k][y] + I.v[k][g]}
                    if Np != Nk: cands.append(g)
                else:
                    if I.v[k][y] + I.v[k][g] >= I.val(k, set(I.sets[k]) - {y, g}): cands.append(g)
            if cands:
                g = max(cands, key=lambda h: (I.v[k][h], -h))
                s.base[k] = frozenset({y, g}); s.kind[k] = 'set'; done = True; break
        if not done: return s


def chains(s, k):
    """need chains from frozen k: lists [k, x1, ..., xt]"""
    I = s.I; fr = s.frozen(); out = []
    def ext(ch):
        last = ch[-1]; (y,) = tuple(s.base[last])
        for x in range(I.n):
            if x in ch or y not in s.needs(x): continue
            if fr[x]:
                ext(ch + [x])
            else:
                out.append(ch + [x])
    ext([k])
    return out


def rotations(s):
    I = s.I; fr = s.frozen(); J = s.junk(); res = []
    for k in range(I.n):
        if not fr[k]: continue
        for ch in chains(s, k):
            base = list(s.base); kind = list(s.kind)
            end = ch[-1]; freed = set(s.base[end])
            for a, b in zip(ch, ch[1:]):
                base[b] = s.base[a]; kind[b] = 'pick'
            pool = (J | freed) & I.R[k]
            for r in range(1, len(pool) + 1):
                for O in itertools.combinations(sorted(pool), r):
                    nb = list(base); nk = list(kind); nb[k] = frozenset(O); nk[k] = 'set'
                    res.append((ch, O, State(I, nb, nk)))
    return res


def extends(I, C, s, B, bb):
    fixed = {g: i for i in range(I.n) for g in s.base[i]}
    own = C.solve(fixed=fixed, extra=bb[B] if B else ())
    if own is not None: assert efx0(I, bundles(I, own))
    return own


def run(I, R, Bs, stats):
    C = Complete(I); bb = {B: C.big_bound(B) for B in Bs if B}
    s0, order = initial(I)
    best = {}
    for B in Bs:
        found = None
        for pol in (1, 2, 0):
            s = upgrade(s0, pol)
            level = [s]; seen = {s.key()}
            for r in range(R + 1):
                if any(extends(I, C, t, B, bb) is not None for t in level):
                    found = r if found is None else min(found, r); break
                if r == R: break
                nxt = []
                for t in level:
                    for ch, O, u in rotations(t):
                        if u.key() not in seen: seen.add(u.key()); nxt.append(u)
                level = nxt
            if found == 0: break
        best[B] = found
    return best


if __name__ == '__main__':
    src = sys.argv[1]
    opt = dict(a[2:].split('=', 1) for a in sys.argv[2:] if a.startswith('--'))
    rng = random.Random(int(opt.get('seed', 1)))
    R = int(opt.get('R', 1)); Bs = [int(x) for x in opt.get('B', '1,2').split(',')]
    print('$ python3 k4/p3/ts.py ' + ' '.join(sys.argv[1:]), flush=True)
    if src == 'ht':
        sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        import c4_chain, ht3
        L = []
        for t in [int(x) for x in opt.get('t', '1,2').split(',')]:
            for v in opt.get('vars', 'HABC'):
                L.append(Inst(*c4_chain.build(t), name=f'H_{t}') if v == 'H' else Inst(*ht3.build(t, v), name=f'H3{v}_{t}'))
    else:
        import dump_rules
        L = dump_rules.load(src, opt, rng)
    cnt = collections.Counter(); ex = collections.defaultdict(list); t0 = time.time()
    for I in L:
        best = run(I, R, Bs, cnt)
        cnt['instances'] += 1
        for B, r in best.items():
            cnt[f'B={B}: rotations ' + ('fail' if r is None else str(r))] += 1
            if r is None: ex[B].append((I.n, I.m, I.name, I.as_json()))
        if src == 'ht': print(I.name, I.n, I.m, best, flush=True)
    print(dict(sorted(cnt.items())), f'{time.time()-t0:.0f}s', flush=True)
    for B in Bs:
        if ex[B]:
            e = min(ex[B], key=lambda e: (e[0], e[1]))
            print(f'smallest failure B={B}, R={R}: n={e[0]} m={e[1]} {e[2]}')
            print('   ', json.dumps(e[3]))
