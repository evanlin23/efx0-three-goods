"""C4K (kgen/rounds.md §4.4): is it a strict connected k = 4 core?  The test is the core claim of
k4/gm4_counterexample.py (check(), claim 1), copied verbatim in logic: degrees 3-4, every good valued, strictly balanced,
strict (all subset sums of each agent's relevant goods distinct), private-good rule (at most d - 2 private goods; two
only with p + q < the rest), connected.  Also the maximum matching size nu and the picks of every order.
    python3 kgen/rounds/c4k_core.py"""
import itertools, json
C4K = [{1: 2030, 4: 1714, 5: 1395, 6: 1806}, {1: 2461, 4: 1674, 5: 1357, 6: 1802},
       {0: 1025, 2: 35, 3: 818, 6: 934}, {0: 1090, 1: 901, 3: 154, 6: 517}]


def v(vals, i, S): return sum(vals[i].get(g, 0) for g in S)


def is_core(vals):
    n = len(vals); m = 1 + max(g for d in vals for g in d)
    R = [set(d) for d in vals]
    deg = [sum(g in R[i] for i in range(n)) for g in range(m)]
    core = all(len(R[i]) in (3, 4) for i in range(n)) and all(d >= 1 for d in deg)
    why = []
    for i in range(n):
        top = max(vals[i].values()); b = top < sum(vals[i].values()) - top; core &= b; why.append(('balanced', i, b))
        sums = [v(vals, i, T) for k in range(1, len(R[i]) + 1) for T in itertools.combinations(sorted(R[i]), k)]
        s = len(set(sums)) == len(sums); core &= s; why.append(('strict', i, s))
        priv = [g for g in R[i] if deg[g] == 1]
        p = len(priv) <= len(R[i]) - 2
        if len(priv) == 2: p &= v(vals, i, priv) < v(vals, i, R[i] - set(priv))
        core &= p; why.append(('private %s' % priv, i, p))
    seen, todo = {0}, [0]
    while todo:
        a = todo.pop()
        for b in range(n):
            if b not in seen and R[a] & R[b]: seen.add(b); todo.append(b)
    core &= len(seen) == n; why.append(('connected', len(seen) == n))
    return core, why


def nu(vals):
    match = {}
    def aug(i, seen):
        for g in sorted(vals[i]):
            if g in seen: continue
            seen.add(g)
            if g not in match or aug(match[g], seen): match[g] = i; return True
        return False
    return sum(aug(i, set()) for i in range(len(vals)))


if __name__ == '__main__':
    core, why = is_core(C4K)
    print('C4K', json.dumps([{str(k): x for k, x in d.items()} for d in C4K]))
    for w in why: print('  ', w)
    print('strict connected k = 4 core:', core, '| maximum matching size nu =', nu(C4K), 'of n =', len(C4K))
