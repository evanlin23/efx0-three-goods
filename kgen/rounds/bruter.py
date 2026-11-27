"""Independent second implementation (pure Python, forward simulation) of the classes of kgen/rounds/rnd.c.

Written from the definitions of k4/sdc.md §29 / k4/ksens.md §6, NOT from rnd.c's backward characterization:
1. enumerate every round explicitly: a set of vertex-disjoint chains x_0..x_t (t >= 0), every choice of the disjoint
   sets H (H_0 inside J + B_{x_t} for t >= 1, inside J for t = 0; H_i inside J), keep it when every chain agent
   strictly gains; apply it (x_0 takes H_0, or B_{x_0} + H_0 when t = 0; x_i takes B_{x_{i-1}} + H_i; the rest of
   B_{x_t} becomes junk);
2. for every distinct resulting base vector, search every placement of the remaining goods and test the raw EFX
   definition (v_i(X_i) >= v_i(X_j - g) for all g in X_j), free or with at most one absorber (an agent holding two or
   more goods outside its base).

Also two rounds (apply step 1 twice, the second round from the bases of the first, then step 2), for confirming a
claimed failure.  Exponential: n <= 4 and m <= 8 or so.

    python3 kgen/rounds/bruter.py '[[v_0], [v_1], ...]' [order...]
"""
import sys, json, itertools
from functools import lru_cache


def sd(vals, order):
    m = len(vals[0]); left = set(range(m)); Y = [None] * len(vals)
    for a in order:
        g = max(left, key=lambda h: (vals[a][h], -h)); Y[a] = g; left.discard(g)
    return Y


def efx(vals, X):
    n = len(X)
    for i in range(n):
        vi = sum(vals[i][g] for g in X[i])
        for j in range(n):
            if i == j: continue
            tot = sum(vals[i][g] for g in X[j])
            for g in X[j]:
                if tot - vals[i][g] > vi: return False
    return True


def completions(vals, bases, A):
    """does some complete EFX allocation contain every base, with at most A absorbers (None = free)?"""
    n, m = len(vals), len(vals[0])
    used = set(g for b in bases for g in b)
    rest = [g for g in range(m) if g not in used]
    for assign in itertools.product(range(n), repeat=len(rest)):
        if A is not None:
            c = [0] * n
            for a in assign: c[a] += 1
            if sum(1 for x in c if x >= 2) > A: continue
        X = [list(b) for b in bases]
        for g, a in zip(rest, assign): X[a].append(g)
        if efx(vals, X): return X
    return None


def v(vals, i, S):
    return sum(vals[i][g] for g in S)


def chains_on(agents, maxlen=None):
    """all sequences of distinct agents (length >= 1, at most maxlen) from `agents`"""
    for L in range(1, min(len(agents), maxlen or len(agents)) + 1):
        for seq in itertools.permutations(agents, L):
            yield seq


def rounds(vals, bases, single=False, maxlen=None):
    """every state (tuple of frozenset bases) reachable by one round (single=True: at most one chain), the empty
    round included"""
    n, m = len(vals), len(vals[0])
    used = set(g for b in bases for g in b)
    J = frozenset(g for g in range(m) if g not in used)
    states = set()
    agents = list(range(n))

    def rec(free_agents, freeJ, cur, nchains):
        states.add(tuple(cur))
        if single and nchains >= 1: return
        # next chain starts at an agent larger than the previous chain's start to avoid repeats (any order works)
        for seq in chains_on(sorted(free_agents), maxlen):
            if nchains and seq[0] < rec_last[-1]: continue
            t = len(seq) - 1
            rest = free_agents - set(seq)
            # choose H sets: each good of freeJ goes to one of the chain agents or stays; plus, for t >= 1, the end's
            # base goods may go to x_0 (each good of B_{x_t} independently)
            jl = sorted(freeJ)
            endb = sorted(bases[seq[-1]]) if t >= 1 else []
            for asg in itertools.product(range(len(seq) + 1), repeat=len(jl)):
                H = [set() for _ in seq]
                for g, a in zip(jl, asg):
                    if a < len(seq): H[a].add(g)
                for take in itertools.product((0, 1), repeat=len(endb)):
                    H0 = set(H[0]) | {g for g, tk in zip(endb, take) if tk}
                    newb = list(cur)
                    ok = True
                    if t == 0:
                        x0 = seq[0]
                        if not H0: ok = False
                        nb0 = frozenset(cur[x0]) | H0
                        if v(vals, x0, nb0) <= v(vals, x0, cur[x0]): ok = False
                        newb[x0] = nb0
                    else:
                        nb0 = frozenset(H0)
                        if v(vals, seq[0], nb0) <= v(vals, seq[0], cur[seq[0]]): ok = False
                        for i in range(1, t + 1):
                            nbi = frozenset(cur[seq[i - 1]]) | H[i]
                            if v(vals, seq[i], nbi) <= v(vals, seq[i], cur[seq[i]]): ok = False; break
                            newb[seq[i]] = nbi
                        newb[seq[0]] = nb0
                        if any(not cur[seq[i]] for i in range(t)): ok = False   # passed bases are nonempty
                    if not ok: continue
                    usedH = set().union(*H) if H else set()
                    rec_last.append(seq[0])
                    rec(rest, freeJ - usedH, newb, nchains + 1)
                    rec_last.pop()
    rec_last = []
    # note: goods of a chain end's base not taken by x_0 become junk only after the round, so they are not in freeJ
    rec(set(agents), J, [frozenset(b) for b in bases], 0)
    return states


def classify(vals, order, two=False):
    """returns dict: ext_free, ext_1, oc1 (one chain + one absorber), rnd_free, rnd_1, and (two=True) rnd2_1"""
    n = len(vals)
    Y = sd(vals, order)
    b0 = [frozenset([y]) for y in Y]
    out = {'picks': Y}
    out['ext_free'] = completions(vals, b0, None) is not None
    out['ext_1'] = completions(vals, b0, 1) is not None
    S1 = rounds(vals, b0, single=True)
    out['oc1'] = any(completions(vals, list(s), 1) is not None for s in S1)
    SR = rounds(vals, b0)
    out['n_round_states'] = len(SR)
    wf = [s for s in SR if completions(vals, list(s), None) is not None]
    out['rnd_free'] = bool(wf)
    out['rnd_1'] = any(completions(vals, list(s), 1) is not None for s in SR)
    if two and not out['rnd_1']:
        seen = set(); ok2 = False
        for s in SR:
            for s2 in rounds(vals, list(s)):
                if s2 in seen: continue
                seen.add(s2)
                if completions(vals, list(s2), 1) is not None: ok2 = True; break
            if ok2: break
        out['rnd2_1'] = ok2; out['n_round2_states'] = len(seen)
    return out


if __name__ == '__main__':
    vals = json.loads(sys.argv[1])
    orders = [tuple(map(int, sys.argv[2:]))] if len(sys.argv) > 2 else list(itertools.permutations(range(len(vals))))
    seen = set()
    for o in orders:
        Y = tuple(sd(vals, o))
        if Y in seen: continue
        seen.add(Y)
        print(o, classify(vals, o, two=True), flush=True)


def chain_sets(agents):
    """every set of vertex-disjoint chains (sequences of distinct agents, length >= 1) on `agents`"""
    agents = sorted(agents)
    def rec(free, last):
        yield []
        for L in range(1, len(free) + 1):
            for seq in itertools.permutations(sorted(free), L):
                if seq[0] <= last: continue
                for rest in rec(free - set(seq), seq[0]):
                    yield [seq] + rest
    yield from rec(set(agents), -1)


def rounds_pool(vals, bases, receivers=False):
    """ROUND-X (kgen/rounds.md §4): one round of vertex-disjoint chains in which every chain START may take, besides
    junk, goods of the base of ANY chain end of the round (a common pool); receivers take junk only.  Written from the
    definition: choose the chain set, then send every junk good to a chain agent or nowhere and every end-base good to a
    start or nowhere (released); keep it when every chain agent strictly gains.
    receivers=True: ROUND-P, every chain agent (receivers and t = 0 agents too) may take end-base goods."""
    n, m = len(vals), len(vals[0])
    used = set(g for b in bases for g in b)
    J = sorted(g for g in range(m) if g not in used)
    states = set()
    for cs in chain_sets(range(n)):
        if any(not bases[seq[i]] for seq in cs for i in range(len(seq) - 1)): continue
        onchain = [a for seq in cs for a in seq]
        starts = [seq[0] for seq in cs if len(seq) >= 2]
        ends = [seq[-1] for seq in cs if len(seq) >= 2]
        endgoods = sorted(g for e in ends for g in bases[e])
        takers = onchain if receivers else starts
        for asgJ in itertools.product([None] + onchain, repeat=len(J)):
            for asgE in itertools.product([None] + takers, repeat=len(endgoods)):
                H = {a: set() for a in onchain}
                for g, a in zip(J, asgJ):
                    if a is not None: H[a].add(g)
                for g, a in zip(endgoods, asgE):
                    if a is not None: H[a].add(g)
                new = [frozenset(b) for b in bases]; ok = True
                for seq in cs:
                    if len(seq) == 1:
                        a = seq[0]
                        if not H[a]: ok = False; break
                        new[a] = frozenset(bases[a]) | H[a]
                    else:
                        new[seq[0]] = frozenset(H[seq[0]])
                        for i in range(1, len(seq)):
                            new[seq[i]] = frozenset(bases[seq[i - 1]]) | H[seq[i]]
                    for a in seq:
                        if v(vals, a, new[a]) <= v(vals, a, bases[a]): ok = False; break
                    if not ok: break
                if ok: states.add(tuple(new))
    return states


def round_x(vals, order, A=1, receivers=False):
    Y = sd(vals, order); b0 = [frozenset([y]) for y in Y]
    return any(completions(vals, list(s), A) is not None for s in rounds_pool(vals, b0, receivers))
