"""Independent OC1^max checker (proof/k4-p3; conjecture K4.SDC.OC1MAX, k4/sdc.md section 31 on claude/kind-lamport-y8fdme).
Written from the definitions, sharing no code with k4/sdc/oc1_mc2_rand.py:
  - nu: maximum matching of the agent / relevant-good graph (augmenting paths);
  - a pick vector (serial dictatorship) is *maximum* if it matches nu agents;
  - a *one-absorber completion* of bases B: an EFX0 allocation X with X_i containing B_i for all i, in which the junk
    J = goods in no base is distributed so that at most one agent receives two or more junk goods (SAT on
    k4/p3/p3lib.Complete, incremental, every model re-checked by the raw definition);
  - *moves* (k4/sdc.md section 29, official rule): an addition (one agent adds a nonempty set of its own junk goods to
    its base); a chain x_0, ..., x_t (t >= 1, distinct; x_i, i >= 1, takes B_{x_{i-1}} plus own junk H_i and gains;
    every handed-on base B_{x_0}, ..., B_{x_{t-1}} nonempty; x_0 takes a nonempty H_0 of its goods among the unused junk
    and B_{x_t}, worth more than B_{x_0}; the rest of B_{x_t} becomes junk); a ring x_0, ..., x_{r-1} (r >= 2), each
    taking its predecessor's nonempty base plus own junk and gaining.
  check(picks) -> 'picks complete' | 'one move repairs' | 'OC1 fails'
    python3 k4/p3/oc1max.py replay FILE.json     replay {'sets', 'vals', 'picks'} records (one per line or a list)
    python3 k4/p3/oc1max.py selftest N SEED      compare with the coordinator's checker (needs OC1_SRC) on N random
                                                (4, 3) cores with n <= 5, every order
"""
import sys, os, itertools, json, random, collections
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p3lib import Inst, Complete, efx0, bundles, sd


def nu(I):
    match = {}
    def aug(i, seen):
        for g in I.sets[i]:
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen):
                match[g] = i; return True
        return False
    return sum(aug(i, set()) for i in range(I.n))


def subsets(xs):
    xs = list(xs)
    for r in range(len(xs) + 1):
        yield from itertools.combinations(xs, r)


class Checker:
    def __init__(self, I):
        self.I = I; self.C = Complete(I)
        self.S = Cadical153(bootstrap_with=self.C.cl)
        self.cache = {}

    def close(self): self.S.delete()

    def complete(self, base):
        """one-absorber completion of the bases (tuple of frozensets), or None"""
        key = tuple(base)
        if key in self.cache: return self.cache[key]
        I, C = self.I, self.C; n = I.n
        held = set().union(*base); J = [g for g in range(I.m) if g not in held]
        act = C.new(); big = []; cl = []
        for a in range(n):
            b = C.new(); big.append(b); prev1 = None
            for g in J:
                c1 = C.new(); xg = C.x[g][a]
                cl.append([-xg, c1])
                if prev1 is not None:
                    cl.append([-prev1, c1]); cl.append([-xg, -prev1, b])
                prev1 = c1
        enc = CardEnc.atmost(lits=big, bound=1, top_id=C.top, encoding=EncType.seqcounter)
        C.top = max(C.top, enc.nv)
        for c in cl + enc.clauses: self.S.add_clause([-act] + c)
        assum = [act] + [C.x[g][i] for i in range(n) for g in base[i]] + [-C.x[g][n] for g in range(I.m)]
        own = None
        if self.S.solve(assumptions=assum):
            mod = set(l for l in self.S.get_model() if l > 0)
            own = [next(a for a in range(n + 1) if C.x[g][a] in mod) for g in range(I.m)]
            X = bundles(I, own)
            assert efx0(I, X), 'model not EFX0'
            assert all(set(base[i]) <= set(X[i]) for i in range(n))
            assert sum(1 for i in range(n) if len(set(X[i]) - set(base[i])) >= 2) <= 1
        self.S.add_clause([-act])          # retire this query's constraints
        self.cache[key] = own
        return own

    def moves(self, base):
        I = self.I; n = I.n; V = I.val
        held = set().union(*base); J = [g for g in range(I.m) if g not in held]
        out = {}
        def add(nb, tag):
            key = tuple(frozenset(b) for b in nb)
            if key not in out or tag < out[key]: out[key] = tag
        for x in range(n):                                     # additions
            for H in subsets([g for g in J if g in I.R[x]]):
                if H: nb = list(base); nb[x] = base[x] | set(H); add(nb, (0, 1, 'addition'))
        def ext(path, used, take):                             # chains
            xt = path[-1]
            if len(path) >= 2:
                x0 = path[0]
                pool = [g for g in J if g not in used and g in I.R[x0]] + [g for g in base[xt] if g in I.R[x0]]
                for H0 in subsets(pool):
                    if H0 and V(x0, H0) > V(x0, base[x0]):
                        nb = list(base); nb[x0] = frozenset(H0)
                        for i in range(1, len(path)): nb[path[i]] = base[path[i - 1]] | take[i]
                        add(nb, (1, len(path), 'chain'))
            if not base[xt] or len(path) >= n: return
            for y in range(n):
                if y in path: continue
                for H in subsets([g for g in J if g not in used and g in I.R[y]]):
                    if V(y, base[xt] | set(H)) > V(y, base[y]):
                        ext(path + [y], used | set(H), {**take, len(path): frozenset(H)})
        for x in range(n): ext([x], frozenset(), {})
        for r in range(2, n + 1):                              # rings
            for cyc in itertools.permutations(range(n), r):
                if cyc[0] != min(cyc): continue
                def ring(i, used, take):
                    if i == r:
                        nb = list(base)
                        for t in range(r): nb[cyc[t]] = base[cyc[t - 1]] | take[t]
                        add(nb, (2, r, 'ring')); return
                    w, pred = cyc[i], cyc[i - 1]
                    if not base[pred]: return
                    for H in subsets([g for g in J if g not in used and g in I.R[w]]):
                        if V(w, base[pred] | set(H)) > V(w, base[w]): ring(i + 1, used | set(H), {**take, i: frozenset(H)})
                ring(0, frozenset(), {})
        return out

    def check(self, picks):
        base = tuple(frozenset([p]) if p is not None else frozenset() for p in picks)
        if self.complete(base) is not None: return 'picks complete', None
        for st in self.moves(base):
            own = self.complete(st)
            if own is not None: return 'one move repairs', st
        return 'OC1 fails', None

    def simplest_repair(self, picks):
        """the simplest repairing move's tag (kind order: addition < chain < ring, then length), or None"""
        base = tuple(frozenset([p]) if p is not None else frozenset() for p in picks)
        mv = self.moves(base)
        for st, tag in sorted(mv.items(), key=lambda kv: kv[1]):
            if self.complete(st) is not None: return tag
        return None


def all_orders(I, only_max=True):
    N = nu(I); res = collections.Counter()
    for o in itertools.permutations(range(I.n)):
        pk = tuple(sd(I, o))
        if only_max and sum(x is not None for x in pk) != N: continue
        res[pk] += 1
    return res, N


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'replay':
        recs = []
        for line in open(sys.argv[2]):
            line = line.strip()
            if not line: continue
            d = json.loads(line); recs += d if isinstance(d, list) else [d]
        for d in recs:
            I = Inst(d['sets'], d['vals']); K = Checker(I)
            N = nu(I); pk = tuple(d['picks']); r, st = K.check(pk)
            print(f"n={I.n} m={I.m} p={I.p()} nu={N} picks={pk} maximum={sum(x is not None for x in pk) == N}: {r}",
                  (f'via {[sorted(b) for b in st]}' if st else ''))
            K.close()
    elif mode == 'selftest':
        N, SEED = int(sys.argv[2]), int(sys.argv[3])
        sys.path.insert(0, os.environ.get('OC1_SRC', ''))
        from oc1_mc2_rand import Inst as CInst
        from p3lib import random_core43, random_types
        rng = random.Random(SEED); agree = dis = 0; cnt = collections.Counter()
        for t in range(N):
            rc = None
            while rc is None: rc = random_core43(rng, rng.choice([3, 4, 5]))
            m, sets = rc; vals = random_types(rng, sets, m)
            I = Inst(sets, vals, m); K = Checker(I); CI = CInst(sets, vals)
            pks, _ = all_orders(I, only_max=False)
            for pk in pks:
                a = K.check(pk)[0]; b = CI.check(pk); cnt[a] += 1
                if a == b: agree += 1
                else: dis += 1; print('DISAGREE', json.dumps({'sets': sets, 'vals': vals, 'picks': pk}), a, b)
            K.close()
        print(f'selftest: {agree} pick vectors agree, {dis} disagree; outcomes {dict(cnt)}')
