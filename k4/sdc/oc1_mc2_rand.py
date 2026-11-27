"""OC1 (k4/sdc.md §29) on random strict connected k = 4 cores in the K4.MC2 class (no agent with two private goods),
every order.  After the strict n = 6 core counterexample B< (k4/sdc/oc1_core_cex_verify.py), the open form is
OC1 (and OC1-ED*) on this class.  Coordinator's own code: raw EFX0, own move generator (official rule: chains never hand
on an empty base), own one-absorber completion search; nothing from the repository, no SAT.

Instances: n agents with 3 or 4 goods, at most one private good each, every shared good valued by >= 2 agents,
connected; values random integers, rejected unless strict (disjoint nonempty subsets of R_i differ) and balanced
(2 v_i(g) < v_i(R_i)).  For every instance: every order's serial-dictatorship picks; OC1 holds at a pick vector if it
has a one-absorber completion or one official move (chain or ring) leads to a state that has one.  With 'p' (OC1^p),
pickless agents may take any number of junk goods (only pick holders count as absorbers).

    python3 k4/sdc/oc1_mc2_rand.py N_INST SEED NMIN NMAX [p]"""
import itertools, sys, os, json, random, collections, time, multiprocessing as mp


class Inst:
    def __init__(self, sets, vals):
        self.sets = sets; self.vals = vals; self.n = len(sets); self.m = 1 + max(max(s) for s in sets)
        self.v = [dict(zip(s, x)) for s, x in zip(sets, vals)]; self.R = [set(s) for s in sets]

    def V(self, i, S): return sum(self.v[i].get(g, 0) for g in S)

    def sd(self, order):
        taken = set(); picks = [None] * self.n
        for i in order:
            av = [g for g in self.R[i] if g not in taken]
            if av:
                g = max(av, key=lambda g: self.v[i][g]); picks[i] = g; taken.add(g)
        return tuple(picks)

    def efx0(self, B):
        v = self.v
        for i in range(self.n):
            own = self.V(i, B[i])
            for j in range(self.n):
                if j != i and B[j] and self.V(i, B[j]) - min(v[i].get(h, 0) for h in B[j]) > own: return False
        return True

    def one_absorber(self, base, pfree=False):
        n = self.n; J = [g for g in range(self.m) if all(g not in b for b in base)]
        if pfree:   # pickless agents (empty base) are free sinks; at most one pick holder takes >= 2 junk goods
            sinks = [i for i in range(n) if not base[i]]; holders = [i for i in range(n) if base[i]]
            for a in [None] + holders:
                others = [i for i in holders if i != a]
                for lab in itertools.product(range(len(sinks) + 1 + (a is not None) + len(others)), repeat=len(J)):
                    # label: 0..len(sinks)-1 a sink; then a (if any); then one of the others (each at most once)
                    cnt = collections.Counter(l for l in lab if l >= len(sinks) + (a is not None))
                    if any(c > 1 for c in cnt.values()): continue
                    B = [list(b) for b in base]
                    for g, l in zip(J, lab):
                        if l < len(sinks): B[sinks[l]].append(g)
                        elif a is not None and l == len(sinks): B[a].append(g)
                        else: B[others[l - len(sinks) - (a is not None)]].append(g)
                    if self.efx0(B): return True
            return False
        for a in [None] + list(range(n)):
            for r in range(0 if a is None else 2, len(J) + 1):
                if a is None and r: break
                for S in itertools.combinations(J, r):
                    rest = [g for g in J if g not in S]; others = [i for i in range(n) if i != a]
                    for recv in itertools.permutations(others, len(rest)):
                        B = [list(b) for b in base]
                        if a is not None: B[a] += list(S)
                        for g, i in zip(rest, recv): B[i].append(g)
                        if self.efx0(B): return True
        return False

    def moves(self, base):
        n, R, V = self.n, self.R, self.V
        J = [g for g in range(self.m) if all(g not in b for b in base)]
        res = set(); key = lambda nb: tuple(tuple(sorted(b)) for b in nb)
        sub = lambda xs: itertools.chain.from_iterable(itertools.combinations(xs, r) for r in range(len(xs) + 1))
        for x in range(n):
            for H in sub([g for g in J if g in R[x]]):
                if H:
                    nb = [list(b) for b in base]; nb[x] = list(base[x]) + list(H); res.add(key(nb))

        def ext(path, used, assign):
            xt = path[-1]
            if len(path) >= 2:
                pool = [g for g in J if g not in used and g in R[path[0]]] + [g for g in base[xt] if g in R[path[0]]]
                for H0 in sub(pool):
                    if H0 and V(path[0], H0) > V(path[0], base[path[0]]):
                        nb = [list(b) for b in base]; nb[path[0]] = list(H0)
                        for i in range(1, len(path)): nb[path[i]] = list(base[path[i - 1]]) + list(assign[i])
                        res.add(key(nb))
            if len(path) >= n or not base[xt]: return
            for y in range(n):
                if y in path: continue
                for H in sub([g for g in J if g not in used and g in R[y]]):
                    if V(y, list(base[xt]) + list(H)) > V(y, base[y]):
                        ext(path + [y], used | set(H), {**assign, len(path): H})
        for x in range(n): ext([x], frozenset(), {})
        for r in range(2, n + 1):
            for cyc in itertools.permutations(range(n), r):
                if cyc[0] != min(cyc): continue

                def ring(i, used, assign):
                    if i == r:
                        nb = [list(b) for b in base]
                        for t in range(r): nb[cyc[t]] = list(base[cyc[t - 1]]) + list(assign[t])
                        res.add(key(nb)); return
                    w, pred = cyc[i], cyc[i - 1]
                    if not base[pred]: return
                    for H in sub([g for g in J if g not in used and g in R[w]]):
                        if V(w, list(base[pred]) + list(H)) > V(w, base[w]): ring(i + 1, used | set(H), {**assign, i: H})
                ring(0, frozenset(), {})
        return res

    def check(self, picks, pfree=False):
        base = [[p] if p is not None else [] for p in picks]
        if self.one_absorber(base, pfree): return 'picks complete'
        for st in self.moves(base):
            if self.one_absorber([list(b) for b in st], pfree): return 'one move repairs'
        return 'OC1 fails'


def gen(n, rng):
    while True:
        d = [rng.choice([3, 4]) for _ in range(n)]; p = [rng.choice([0, 1]) for _ in range(n)]
        slots = sum(di - pi for di, pi in zip(d, p)); s = rng.randint(max(2, n - 1), slots // 2)
        sh = [sorted(rng.sample(range(s), d[i] - p[i])) for i in range(n)]
        deg = collections.Counter(g for x in sh for g in x)
        if any(deg[g] < 2 for g in range(s)): continue
        comp = {0}; grow = True
        while grow:
            grow = False
            for j in range(n):
                if j not in comp and any(set(sh[j]) & set(sh[i]) for i in comp): comp.add(j); grow = True
        if len(comp) < n: continue
        sets = []; nxt = s
        for i in range(n):
            sets.append(sh[i] + ([nxt] if p[i] else [])); nxt += p[i]
        vals = []
        for i in range(n):
            while True:
                x = [rng.randint(1, 40) for _ in sets[i]]
                if 2 * max(x) >= sum(x): continue
                sums = collections.defaultdict(list); ok = True
                for r in range(1, len(x) + 1):
                    for T in itertools.combinations(range(len(x)), r): sums[sum(x[k] for k in T)].append(set(T))
                for L in sums.values():
                    if any(not (a & b) for a, b in itertools.combinations(L, 2)): ok = False; break
                if ok: break
            vals.append(x)
        return sets, vals


def job(args):
    n, seed, pfree = args
    rng = random.Random(seed); sets, vals = gen(n, rng); I = Inst(sets, vals)
    picks = collections.Counter(I.sd(o) for o in itertools.permutations(range(n)))
    C = collections.Counter(); bad = []
    for pk, c in picks.items():
        r = I.check(pk, pfree); C[r] += c
        if r == 'OC1 fails': bad.append(pk)
    return n, seed, sets, vals, C, bad


if __name__ == '__main__':
    N, SEED, NMIN, NMAX = map(int, sys.argv[1:5]); PF = len(sys.argv) > 5 and sys.argv[5] == 'p'
    print('$ python3 k4/sdc/oc1_mc2_rand.py', *sys.argv[1:], flush=True)
    t0 = time.time(); T = collections.Counter()
    tasks = [(NMIN + t % (NMAX - NMIN + 1), SEED * 1000003 + t, PF) for t in range(N)]
    with mp.Pool(int(os.environ.get('PROCS', mp.cpu_count()))) as pool:
        for n, seed, sets, vals, C, bad in pool.imap_unordered(job, tasks):
            T['instances n=%d' % n] += 1
            for k, c in C.items(): T['n=%d orders: %s' % (n, k)] += c
            if bad:
                T['n=%d instances with a failing order' % n] += 1
                print('OC1 FAILS', json.dumps({'n': n, 'seed': seed, 'sets': sets, 'vals': vals, 'picks': bad,
                                               'orders': dict(C)}), flush=True)
    for k in sorted(T): print(k, T[k])
    print('time %.0f s' % (time.time() - t0))
