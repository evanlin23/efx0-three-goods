#!/usr/bin/env python3
"""Independent check of the data behind Conjecture BT4 (K4.ZF1.BT4, `k4/zmove_f1.md` §4): the referee's second
implementation (PR #91 review). EVIDENCE tooling. Imports nothing from the repository and does not use
configurations, Lemma K or Lemma 0: it works on the pre-allocations of `k4/c4x.md` §1 directly.

Definitions (`k4/c4x.md` §1, `k4/sx.md` §1):
  a pre-allocation P: disjoint bases B_i ⊆ R_i, |B_i| <= 2; junk J = M - U B_i; needs N_i = {h in R_i - B_i :
  v_i(h) > v_i(B_i)}; NA = U N_i; P is valid iff (V1) J ∩ NA = ∅ and (V2) no good of a two-good base is in NA.
  Frozen agents: base of one good, that good in NA. |F| = |NA|. f = the fewest frozen agents over the valid P.
  The removal-only deficit: S = slots of the free agents (2 - |B_i| each); if |J| - S <= 0, def(P) = |J| - S;
  otherwise def(P) = min over free owners o and C ⊆ J such that X = B_o ∪ (J - C) threatens no agent j != o holding
  B_j alone (max_{h in X} v_j(X - h) <= v_j(B_j)) of |C| - S_o(C), where S_o(C) counts the slots of the agents j != o
  with frozen status recomputed after replacing o's needs by N_o^X = {h in R_o - X : v_o(h) > v_o(X)}.
  The key of a P with f frozen agents is its set of frozen agents with their goods; def*(κ) = min def(P) over the
  min-frozen P of key κ. At f = 1 a key is one agent i frozen on one good g; "completable" means def*(κ) <= 0.
  Big-top (`k4/c4min_f1.md` §1): |R_i| = 4 and v(a) > v(b) + v(c) for its goods a > b > c > d.

Only P with |NA| = 1 are needed at f = 1 (|F| = |NA|): NA = {g}, g is the base of the one frozen agent i, every
other base avoids g and has needs inside {g}, and some agent needs g (otherwise NA = ∅ and f = 0).

usage:
  python3 k4/zf1_indep.py --eshape [--sets=JSON] [--procs=N]   every strict balanced profile of the (E)-shaped core
                                                              with the first three agents big-top on good 0
  python3 k4/zf1_indep.py DUMP.jsonl.gz ...                   every f = 1 key of every profile of PR #80's dumps
  python3 k4/zf1_indep.py --n3 [--every=E] DUMP.jsonl.gz ...  n = 3: who values g at the non-completable keys"""
import collections, gzip, itertools, json, multiprocessing, sys, time


class Profile:
    def __init__(self, sets, vals, m):
        self.n = len(sets); self.m = m
        self.goods = [list(S) for S in sets]
        self.R = [sum(1 << g for g in S) for S in sets]
        self.vg = [dict(zip(S, V)) for S, V in zip(sets, vals)]
        self.tab = []
        for i in range(self.n):
            t = {}
            for k in range(len(sets[i]) + 1):
                for T in itertools.combinations(sets[i], k):
                    t[sum(1 << g for g in T)] = sum(self.vg[i][g] for g in T)
            sums = [s for mk, s in t.items() if mk]
            assert len(set(sums)) == len(sums), 'profile not strict'
            assert 2 * max(self.vg[i].values()) < sum(self.vg[i].values()), 'agent not strictly balanced'
            self.tab.append(t)
        self.ALL = (1 << m) - 1

    def v(self, i, X): return self.tab[i][X & self.R[i]]

    def needs(self, i, B):
        vb = self.v(i, B); out = 0
        for g in self.goods[i]:
            if not B >> g & 1 and self.vg[i][g] > vb: out |= 1 << g
        return out

    def theta(self, j, X):
        best = -1
        for h in range(self.m):
            if X >> h & 1:
                best = max(best, self.v(j, X & ~(1 << h)))
        return best

    def bases(self, i):
        gs = self.goods[i]
        return [sum(1 << g for g in T) for k in (1, 2) for T in itertools.combinations(gs, k)]

    def bigtop(self, i):
        if len(self.goods[i]) != 4: return False
        a, b, c, d = sorted(self.vg[i].values(), reverse=True)
        return a > b + c

    def top(self, i): return max(self.goods[i], key=lambda g: self.vg[i][g])


def f_is_zero(p):
    """some valid P without frozen agents: disjoint bases with no needs"""
    opts = [[B for B in p.bases(i) if p.needs(i, B) == 0] for i in range(p.n)]

    def rec(i, used):
        if i == p.n: return True
        return any(not B & used and rec(i + 1, used | B) for B in opts[i])
    return rec(0, 0)


def one_frozen_states(p, i, g):
    """every valid P whose only frozen agent is i, frozen on {g} (so NA = {g})"""
    G = 1 << g
    if p.needs(i, G): return  # i's needs would lie outside NA = {g}
    others = [y for y in range(p.n) if y != i]
    opts = {y: [B for B in p.bases(y) if not B & G and not (p.needs(y, B) & ~G)] for y in others}
    cur = {i: G}

    def rec(k, used):
        if k == len(others):
            NA = 0
            for y, B in cur.items(): NA |= p.needs(y, B)
            assert NA in (0, G)
            if NA == G: yield dict(cur)
            return
        y = others[k]
        for B in opts[y]:
            if not B & used:
                cur[y] = B
                yield from rec(k + 1, used | B)
                del cur[y]
    yield from rec(0, G)


def deficit_le0(p, P):
    """def(P) <= 0 for a valid P (removal-only deficit, k4/c4x.md §1)"""
    n = p.n
    NAi = {j: p.needs(j, P[j]) for j in range(n)}
    NA = 0
    for j in range(n): NA |= NAi[j]
    frozen = {j for j in range(n) if bin(P[j]).count('1') == 1 and P[j] & NA}
    J = p.ALL
    for j in range(n): J &= ~P[j]
    S = sum(2 - bin(P[j]).count('1') for j in range(n) if j not in frozen)
    if bin(J).count('1') - S <= 0: return True
    Jl = [h for h in range(p.m) if J >> h & 1]
    for o in range(n):
        if o in frozen: continue
        cap = sum(2 - bin(P[j]).count('1') for j in range(n) if j != o)
        NAo = 0
        for j in range(n):
            if j != o: NAo |= NAi[j]
        for k in range(0, min(cap, len(Jl)) + 1):
            for Ct in itertools.combinations(Jl, k):
                C = sum(1 << h for h in Ct)
                X = P[o] | (J & ~C)
                if any(p.theta(j, X) > p.v(j, P[j]) for j in range(n) if j != o): continue
                NAX = NAo | p.needs(o, X)
                So = sum(2 - bin(P[j]).count('1') for j in range(n)
                         if j != o and not (bin(P[j]).count('1') == 1 and P[j] & NAX))
                if k <= So: return True
    return False


def f1_keys(p):
    """None if f = 0; otherwise [(i, g, completable)] for the keys with one frozen agent ([] means f >= 2)"""
    if f_is_zero(p): return None
    out = []
    for i in range(p.n):
        for g in p.goods[i]:
            states = list(one_frozen_states(p, i, g))
            if states:
                out.append((i, g, any(deficit_le0(p, P) for P in states)))
    return out


# ---------------------------------------------------------------- strict balanced types of 4 goods, from scratch
def types4():
    """one value vector per order type of the 15 nonempty subset sums, strict and strictly balanced"""
    reps = {}
    for v in itertools.product(range(1, 13), repeat=4):
        sums = [sum(v[k] for k in range(4) if S >> k & 1) for S in range(1, 16)]
        if len(set(sums)) < 15 or 2 * max(v) >= sum(v): continue
        sig = tuple(sorted(range(15), key=lambda s: sums[s]))
        reps.setdefault(sig, v)
    return list(reps.values())


def eshape_job(args):
    sets, m, vx, rest = args
    cnt = collections.Counter(); bad = []
    for v1, v2, vw in rest:
        p = Profile(sets, [vx, v1, v2, vw], m)
        cnt['profiles'] += 1
        keys = f1_keys(p)
        if keys is None: cnt['f = 0'] += 1; continue
        if not keys: cnt['f >= 2'] += 1; continue
        cnt['f = 1'] += 1
        if not any(i == 0 and g == 0 for i, g, _ in keys): cnt['(0, x) not a key'] += 1
        for i, g, comp in keys:
            bt = p.bigtop(i)
            tag = 'key (%d, agent %d), frozen agent %s' % (g, i, 'big-top' if bt else 'not big-top')
            cnt[tag + ': ' + ('completable' if comp else 'NON-completable')] += 1
            if bt and not comp: bad.append((sets, [vx, v1, v2, vw], m, g, i))
    return cnt, bad


def run_eshape(opts):
    sets = json.loads(opts['sets']) if 'sets' in opts else [[0, 1, 2, 3], [0, 4, 5, 6], [0, 7, 8, 6], [9, 10, 1, 4]]
    m = 1 + max(g for S in sets for g in S)
    T = types4()
    print('# strict balanced types of 4 goods:', len(T))

    def bt_on_first(v): return v[0] == max(v) and v[0] > sum(sorted(v[1:], reverse=True)[:2])
    deg = [sum(g in S for S in sets) for g in range(m)]
    priv = [k for k, g in enumerate(sets[3]) if deg[g] == 1]
    BT = [v for v in T if bt_on_first(v)]
    W = [v for v in T if len(priv) != 2 or v[priv[0]] + v[priv[1]] < sum(v) - v[priv[0]] - v[priv[1]]]
    print('# sets', sets, 'm', m, '; agents 0-2 big-top on good 0:', len(BT), 'types each; agent 3 (C4):', len(W))
    jobs = [(sets, m, vx, [(v1, v2, vw) for vw in W]) for vx in BT for v1 in BT for v2 in BT]
    cnt = collections.Counter(); bad = []
    with multiprocessing.Pool(int(opts.get('procs', multiprocessing.cpu_count()))) as pool:
        for c, b in pool.imap_unordered(eshape_job, jobs):
            cnt.update(c); bad.extend(b)
    for b in bad: print('NON-completable big-top key', json.dumps(b))
    return cnt


def load(path):
    op = gzip.open if path.endswith('.gz') else open
    with op(path, 'rt') as fh:
        for line in fh:
            if line.strip(): yield json.loads(line)


def run_dumps(paths):
    cnt = collections.Counter()
    for path in paths:
        for rec in load(path):
            p = Profile(rec['sets'], rec['vals'], rec['m'])
            keys = f1_keys(p)
            if not keys: cnt['profiles with f != 1, n = %d' % p.n] += 1; continue
            for i, g, comp in keys:
                if comp: continue
                bt = p.bigtop(i)
                cnt['non-completable keys, n = %d' % p.n] += 1
                if bt:
                    cnt['non-completable keys with x big-top, n = %d' % p.n] += 1
                    if p.n >= 4: print('NON-completable big-top key at n >= 4', json.dumps(rec), g, i)
    return cnt


def run_n3(paths, every):
    """n = 3: at each non-completable key (g, x), how many free agents value g, and are they big-top on g"""
    cnt = collections.Counter(); idx = 0
    for path in paths:
        for rec in load(path):
            idx += 1
            if (idx - 1) % every: continue
            p = Profile(rec['sets'], rec['vals'], rec['m'])
            keys = f1_keys(p)
            if not keys: continue
            cnt['profiles'] += 1
            for x, g, comp in keys:
                if comp: continue
                free = [y for y in range(p.n) if y != x]
                val_g = [y for y in free if p.R[y] >> g & 1]
                bt_g = [y for y in free if p.bigtop(y) and p.top(y) == g]
                if p.bigtop(x):
                    cnt['non-completable keys, x big-top: %d free agent(s) value g' % len(val_g)] += 1
                else:
                    cnt['non-completable keys, x not big-top: %d of %d free agents big-top on g'
                        % (len(bt_g), len(free))] += 1
    return cnt


def main(argv):
    opts = {}; ins = []
    for a in argv:
        if a.startswith('--'):
            k, _, v = a[2:].partition('='); opts[k] = v
        else: ins.append(a)
    print('# command: python3 k4/zf1_indep.py ' + ' '.join(argv))
    t0 = time.time()
    if 'eshape' in opts: cnt = run_eshape(opts)
    elif 'n3' in opts: cnt = run_n3(ins, int(opts.get('every', 1)))
    else: cnt = run_dumps(ins)
    for k in sorted(cnt): print('  %-72s %d' % (k, cnt[k]))
    print('done; time %.0f s' % (time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
