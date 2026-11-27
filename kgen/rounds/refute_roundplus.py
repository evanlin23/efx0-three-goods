"""Refutation of ROUND+ (kgen/rounds.md §3): strictly positive additive values, one serial-dictatorship start from which
no round of vertex-disjoint improving chains (k4/ksens.md §6) reaches bases with a complete EFX completion, free or
with one absorber.  Pure Python, raw definitions only; shares no code with rnd.c, bruter.py or ocsat.

The argument (written proof in kgen/rounds.md §3; this script checks its finite part):
  (R1) A round from the picks only reaches allocations X with v_i(X_i) >= v_i(y_i) for every i (MD): agents off the
       chains keep their pick, chain agents strictly gain, and the completion only adds goods.
  (R2) After one round from singleton picks, every base contains at most one pick of another agent, and an agent a
       with y_a outside X_a lay on a chain with t >= 1, so its base B_a (inside X_a) satisfies v_a(B_a) > v_a(y_a).
  Hence X is unreachable as soon as some agent a has y_a not in X_a and
       max over f in (X_a cap foreign picks) + {none} of  v_a({f} + (X_a cap J))  <=  v_a(y_a)      ("starved").
  The script enumerates all n^m allocations, keeps the EFX ones (raw definition), keeps those that satisfy MD, and
  checks that each has a starved agent.  It also prints an explicit two-round repair, found by forward search over
  every round (every chain set and every choice of junk sets), and checked against the raw definition.

    python3 kgen/rounds/refute_roundplus.py            # RD5+ and the other confirmed instances
"""
import itertools, sys, json

INSTANCES = [
    ('RD5+ (RD5 of k4/ksens.md §6 with v0(4) = 23, values x100, every zero -> 1)',
     [[2600, 5700, 1, 4400, 2300, 3300, 1], [1, 1200, 1100, 600, 1, 1, 1], [1, 900, 800, 600, 100, 1, 1],
      [3600, 1, 5300, 1, 1, 4700, 400]], (0, 3, 1, 2)),
    ('C4G (climb from GM4-G lifted)',
     [[304, 35, 1, 2864, 610, 2535, 950], [432, 643, 29, 1067, 71, 2469, 764], [90, 582, 165, 1265, 981, 2483, 1970],
      [434, 642, 29, 1068, 69, 2467, 764]], (2, 1, 3, 0)),
    ('C5a (n = 5, m = 8, climb from the pw family)',
     [[2063, 1345, 89, 17, 50, 1895, 2387, 2026], [2733, 1, 1, 1, 1, 1662, 3000, 1984],
      [1955, 4, 976, 1, 594, 1320, 1743, 1437], [1954, 5, 978, 1, 595, 1320, 1742, 1436],
      [2467, 110, 449, 258, 1, 1463, 2853, 1733]], (0, 4, 2, 3, 1)),
]


def sd(V, order):
    left = set(range(len(V[0]))); y = [None] * len(V)
    for a in order:
        best = None
        for g in sorted(left):
            if best is None or V[a][g] > V[a][best]: best = g
        y[a] = best; left.remove(best)
    return y


def efx(V, X):
    for i in range(len(X)):
        own = sum(V[i][g] for g in X[i])
        for j in range(len(X)):
            if i != j and X[j]:
                if sum(V[i][g] for g in X[j]) - min(V[i][g] for g in X[j]) > own: return False
    return True


def allocations(n, m):
    for own in itertools.product(range(n), repeat=m):
        X = [[] for _ in range(n)]
        for g, a in enumerate(own): X[a].append(g)
        yield X


def starved(V, X, y, J):
    """agents a with y_a outside X_a whose best one-round base inside X_a does not beat y_a"""
    n = len(X); out = []
    picks = set(y)
    for a in range(n):
        if y[a] in X[a]: continue
        jv = sum(V[a][g] for g in X[a] if g in J)
        foreign = [g for g in X[a] if g in picks]
        best = jv + max([V[a][f] for f in foreign] + [0])
        if best <= V[a][y[a]]: out.append((a, best, V[a][y[a]]))
    return out


# ---- explicit forward search for a two-round repair (independent of the enumeration above) ----
def val(V, i, S): return sum(V[i][g] for g in S)


def one_round(V, bases, junk):
    """every (new bases, new junk) after one round of vertex-disjoint chains (including the empty round)"""
    n = len(V); res = []

    def rec(free, fj, cur, rel, last):
        res.append((tuple(map(frozenset, cur)), frozenset(fj | rel)))
        for L in range(1, len(free) + 1):
            for seq in itertools.permutations(sorted(free), L):
                if seq[0] < last: continue
                if any(not cur[seq[i]] for i in range(L - 1)): continue
                jl = sorted(fj); endb = sorted(cur[seq[-1]]) if L > 1 else []
                for asg in itertools.product(range(L + 1), repeat=len(jl)):
                    H = [set() for _ in seq]
                    for g, k in zip(jl, asg):
                        if k < L: H[k].add(g)
                    for take in itertools.product((0, 1), repeat=len(endb)):
                        T = {g for g, t in zip(endb, take) if t}
                        new = list(cur); ok = True
                        if L == 1:
                            nb = set(cur[seq[0]]) | H[0]
                            ok = bool(H[0]) and val(V, seq[0], nb) > val(V, seq[0], cur[seq[0]])
                            new[seq[0]] = nb; released = set()
                        else:
                            new[seq[0]] = H[0] | T
                            ok = val(V, seq[0], new[seq[0]]) > val(V, seq[0], cur[seq[0]])
                            for i in range(1, L):
                                new[seq[i]] = set(cur[seq[i - 1]]) | H[i]
                                ok = ok and val(V, seq[i], new[seq[i]]) > val(V, seq[i], cur[seq[i]])
                            released = set(endb) - T
                        if ok:
                            used = set().union(*H)
                            rec(free - set(seq), fj - used, new, rel | released, seq[0])
    rec(set(range(n)), set(junk), [set(b) for b in bases], set(), -1)
    return res


def completion(V, bases, rest, A=1):
    n = len(V); rest = sorted(rest)
    for asg in itertools.product(range(n), repeat=len(rest)):
        c = [0] * n
        for a in asg: c[a] += 1
        if sum(1 for x in c if x >= 2) > A: continue
        X = [sorted(b) for b in bases]
        for g, a in zip(rest, asg): X[a].append(g)
        if efx(V, X): return X
    return None


def two_round_repair(V, y):
    m = len(V[0]); J = set(range(m)) - set(y)
    b0 = [frozenset([g]) for g in y]
    for b1, j1 in one_round(V, b0, J):
        for b2, j2 in one_round(V, b1, j1):
            X = completion(V, b2, j2)
            if X is not None: return b1, b2, X
    return None


def main():
    allok = True
    for name, V, order in INSTANCES:
        n, m = len(V), len(V[0])
        assert all(x > 0 for r in V for x in r)
        y = sd(V, order); J = set(range(m)) - set(y)
        print('==', name, '\n   n %d, m %d, order %s, picks %s, junk %s' % (n, m, order, y, sorted(J)))
        nefx = 0; md = []
        for X in allocations(n, m):
            if efx(V, X):
                nefx += 1
                if all(sum(V[i][g] for g in X[i]) >= V[i][y[i]] for i in range(n)): md.append(X)
        print('   EFX allocations %d, of which value-dominate the picks (MD): %d' % (nefx, len(md)))
        ok = True
        for X in md:
            s = starved(V, X, y, J)
            print('     MD', X, 'starved agents (a, best base value, v_a(y_a)):', s)
            if not s: ok = False
        print('   every MD allocation has a starved agent:', ok)
        if n <= 4:
            rep = two_round_repair(V, y)
            if rep:
                b1, b2, X = rep
                print('   two-round repair: after round 1 bases', [sorted(b) for b in b1], '; after round 2',
                      [sorted(b) for b in b2], '; completion', X, 'EFX', efx(V, X))
            else:
                print('   no two-round repair found'); ok = False
        allok &= ok
    print('ALL CLAIMS HOLD' if allok else 'SOME CLAIM FAILS')
    sys.exit(0 if allok else 1)


if __name__ == '__main__':
    main()
