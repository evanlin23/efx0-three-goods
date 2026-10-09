"""LB+ (K3ALG's Stage L) with pluggable rules, for testing simplifications (branch proof/k3-simplify).

Input: a ranking profile `rank` (rank[i] = (a_i, b_i, c_i), agent i's three goods, best first) on goods 0..m-1;
goods nobody ranks are worthless. Every agent is balanced (a <= b + c); by Lemma L5 of the paper, EFX0 then depends
only on the rankings, and we check it with the values 4, 3, 2.

lbx(rank, m, leader=..., fix=...) returns (X, tag): X[g] = the agent that receives good g (None if the variant
gives up), tag = which branch was taken. With leader='index' and fix='rotate' it is K3ALG's Stage L exactly
(validated against k3/k3algo.py `fast` by `python3 lbx.py --validate`).

Definitions follow paper/k3/long.tex Section 4 (picks, R1 priority, blocks, needs, NA, frozen, terminals, upgrades,
slots, exposed agents, HitSet, need chains, rotation).
"""
import sys, itertools, random

VAL = (4, 3, 2)

# ------------------------------------------------------------------------------------------------ the state
class State:
    def __init__(self, rank, m):
        self.rank, self.m, self.n = rank, m, len(rank)
        self.pos = [{g: t for t, g in enumerate(r)} for r in rank]   # 0 = a, 1 = b, 2 = c

    def phase1(self, leader, pre=()):
        """Serial dictatorship with R1 priority. `leader(st, unproc, free)` chooses the agent of an insertion step.
        Agents in `pre` are skipped (pre-assigned elsewhere). Returns order, picks Y, blocks blk, leftover set."""
        free = set(range(self.m)) - {g for x in pre for g in self.pre_goods(x)}
        unproc = [i for i in range(self.n) if i not in pre]
        order, Y, blk, nb = [], [None] * self.n, [0] * self.n, 0
        while unproc:
            c = next((i for i in unproc if sum(g in free for g in self.rank[i]) <= 2), None)
            if c is None:
                c = leader(self, unproc, free); nb += 1
            blk[c] = nb
            Y[c] = next((g for g in self.rank[c] if g in free), None)
            free.discard(Y[c]); order.append(c); unproc.remove(c)
        return order, Y, blk, free

    def pre_goods(self, x): return (self.rank[x][1], self.rank[x][2])

    def needs(self, i, Y, U):
        if i in U: return ()
        if Y[i] is None: return self.rank[i]
        return self.rank[i][:self.pos[i][Y[i]]]

    def NA(self, Y, U): return {g for i in range(self.n) for g in self.needs(i, Y, U)}

    def junk(self, Y, U):
        used = {g for g in Y if g is not None} | {self.rank[u][2] for u in U}
        return [g for g in range(self.m) if g not in used]

    def upgrades(self, Y, U):
        U = list(U)
        while True:
            J = set(self.junk(Y, U)); na = self.NA(Y, U)
            k = next((k for k in range(self.n) if k not in U and Y[k] == self.rank[k][1]
                      and self.rank[k][2] in J and self.rank[k][1] not in na), None)
            if k is None: return U
            U = [k] + U

    def caps(self, Y, U):
        na = self.NA(Y, U)
        return [0 if (i in U or (Y[i] is not None and Y[i] in na)) else (2 if Y[i] is None else 1)
                for i in range(self.n)]

    def frozen(self, i, Y, U, na): return i not in U and Y[i] is not None and Y[i] in na

    def base(self, o, Y, U):
        if o in U: return {self.rank[o][1], self.rank[o][2]}
        return {Y[o]} if Y[o] is not None else set()

    def exposed(self, o, Y, U):
        J = set(self.junk(Y, U)); W = J | self.base(o, Y, U)
        return [x for x in range(self.n) if x != o and x not in U and Y[x] == self.rank[x][0]
                and self.rank[x][1] in W and self.rank[x][2] in W]

    def hitset(self, E, Y, U):
        J = set(self.junk(Y, U))
        one = lambda z: self.rank[z][1] if self.rank[z][1] in J else self.rank[z][2]
        for x in E:
            for y in E:
                if x == y: continue
                for g in (self.rank[x][1], self.rank[x][2]):
                    if g in J and g in (self.rank[y][1], self.rank[y][2]):
                        return [g] + [one(z) for z in E if z != x and z != y]
        return [one(z) for z in E]

    def complete(self, Y, U, o, H):
        """K3ALG's Complete(o, H): picks, c_u, then the list H + rest of junk through the windows of the agents
        other than o (cap(i) consecutive entries each, index order); what is left goes to o."""
        X = [None] * self.m
        for i in range(self.n):
            if Y[i] is not None: X[Y[i]] = i
        for u in U: X[self.rank[u][2]] = u
        J = self.junk(Y, U); L = list(H) + [g for g in J if g not in H]
        cap = self.caps(Y, U)
        for i in range(self.n):
            if i == o: continue
            for g in L[:cap[i]]:
                if X[g] is None: X[g] = i
            L = L[cap[i]:]
        for g in J:
            if X[g] is None: X[g] = o
        return X

# ------------------------------------------------------------------------------------------------ leader rules
def lead_index(st, unproc, free): return unproc[0]

LEADERS = {'index': lead_index}

# ------------------------------------------------------------------------------------------------ the run
def owner_step(st, Y, U, order, blk):
    """After the upgrades: returns ('noowner', X) / ('owner_r', X) / ('bad', r) (r is not a valid owner)."""
    J = st.junk(Y, U); cap = st.caps(Y, U)
    if len(J) <= sum(cap): return 'noowner', st.complete(Y, U, None, [])
    r = [i for i in order if i not in U][-1]
    H = st.hitset(st.exposed(r, Y, U), Y, U)
    if len(H) <= sum(cap) - cap[r]: return 'owner_r', st.complete(Y, U, r, H)
    return 'bad', r

def rotate(st, Y, U, order, blk, r):
    E = st.exposed(r, Y, U)
    k = next(x for x in E if blk[x] == blk[r])
    na = st.NA(Y, U); chain = [k]
    for j in order[order.index(k) + 1:]:
        cur = chain[-1]
        if st.frozen(cur, Y, U, na) and j not in U and Y[cur] is not None and st.pos[j].get(Y[cur], 3) < (3 if Y[j] is None else st.pos[j][Y[j]]):
            chain.append(j)
    Y2 = list(Y)
    for s in range(1, len(chain)): Y2[chain[s]] = Y[chain[s - 1]]
    Y2[k] = st.rank[k][1]; U2 = [k] + U
    J2 = st.junk(Y2, U2); cap2 = st.caps(Y2, U2)
    if len(J2) <= sum(cap2): return st.complete(Y2, U2, None, []), 'rot_noowner'
    return st.complete(Y2, U2, k, st.hitset(st.exposed(k, Y2, U2), Y2, U2)), 'rot_owner_k'

def lbx(rank, m, leader='index', fix='rotate'):
    st = State(rank, m)
    lead = LEADERS[leader] if isinstance(leader, str) else leader
    order, Y, blk, _ = st.phase1(lead)
    U = st.upgrades(Y, [])
    tag, out = owner_step(st, Y, U, order, blk)
    if tag != 'bad': return out, tag
    r = out
    if fix == 'rotate': return rotate(st, Y, U, order, blk, r)
    if fix == 'none': return None, 'bad'
    return FIXES[fix](st, lead, Y, U, order, blk, r)

FIXES = {}

# ------------------------------------------------------------------------------------------------ checks
def efx0(rank, m, X):
    n = len(rank); v = [dict(zip(r, VAL)) for r in rank]
    B = [[g for g in range(m) if X[g] == i] for i in range(n)]
    for i in range(n):
        own = sum(v[i].get(g, 0) for g in B[i])
        for j in range(n):
            if i == j or not B[j]: continue
            s = sum(v[i].get(g, 0) for g in B[j]); mn = min(v[i].get(g, 0) for g in B[j])
            if s - mn > own: return False
    return True

def core_profiles(maxn, certs='results/certs_lb_2_6.json.gz', disc='results/certs_lb_disconnected_4_6.json.gz', sample=0, seed=1, minn=2):
    """Every ranking profile (or `sample` random ones per core) of every certified core with minn <= n <= maxn."""
    import json, gzip, os
    root = os.path.join(os.path.dirname(__file__), '..', '..')
    recs = []
    for p in dict.fromkeys((certs, disc)):
        recs += [r for r in json.load(gzip.open(os.path.join(root, p))) if minn <= r['n'] <= maxn]
    perms = list(itertools.permutations(range(3)))
    rng = random.Random(seed)
    for rec in recs:
        n, m, sets = rec['n'], rec['m'], rec['sets']
        profs = ([tuple(rng.randrange(6) for _ in range(n)) for _ in range(sample)] if sample
                 else itertools.product(range(6), repeat=n))
        for prof in profs:
            yield n, m, [tuple(sets[i][p] for p in perms[prof[i]]) for i in range(n)]

def validate(maxn=4, rand=20000, seed=3):
    sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
    import k3algo
    cnt = 0; tags = {}
    def one(rank, m):
        n = len(rank); v = [dict(zip(r, VAL)) for r in rank]
        X1, info = k3algo.fast(n, m, v)
        X2, tag = lbx(rank, m)
        assert X1 == X2 and info['branch'] == tag, (rank, m, X1, X2, info, tag)
        assert efx0(rank, m, X2)
        tags[tag] = tags.get(tag, 0) + 1
    for n, m, rank in core_profiles(maxn): one(rank, m); cnt += 1
    rng = random.Random(seed)
    for _ in range(rand):
        n = rng.randint(2, 8); m = rng.randint(3, 2 * n + 2)
        one([tuple(rng.sample(range(m), 3)) for _ in range(n)], m); cnt += 1
    print(f"validate: {cnt} profiles (every profile of every core n <= {maxn}, plus {rand} random profiles n <= 8): "
          f"lbx == k3algo.fast (allocation and branch) on all; all EFX0. branches {tags}")

if __name__ == '__main__':
    if '--validate' in sys.argv: validate()
