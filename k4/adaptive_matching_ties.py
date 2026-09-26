"""Do the failures of the matching-based rules 17, 18 and 25 (k4/adaptive.md §5) depend on how ties between optimal
matchings are broken? k4/adaptive.c takes the matching its successive-shortest-path computation ends with (Bellman-Ford
scanning the agents in index order, each agent's first-choice edge before its second-choice edge; the first strictly
shorter path wins); when a profile has several optimal matchings (largest size, then most first choices), which one it
returns is a property of that computation, not a tie-break by index.

This script is independent of adaptive.c's matching and of its LB4r: for a profile it enumerates every optimal
matching by brute force, derives each insertion sequence the rule can produce under some choice of optimal matchings
(rules 17 and 18: one matching on all agents and goods; rule 25: a matching recomputed at every insertion step on the
unprocessed agents and remaining goods, so a tree of choices), and computes the fewest rotations LB4r needs on each
with the LB4r model of PR #33 (k4/c4_verify_H/lb4r.py; C4VERIFY_DIR overrides), as attempts/k4_adaptive_attempts.py
does. A failure is tie-robust if every such sequence needs two rotations.
Usage: adaptive_matching_ties.py                       the profiles of attempts/k4-adaptive-matching.md
       adaptive_matching_ties.py --deep=LOG            every 'DEEP ... w=W' line of LOG (output of k4/adaptive_run.py
                                                       -AR -r3 -K2, R in 17, 18, 25 read from each run's header line),
                                                       each a leaf's representative profile of weight W"""
import itertools, os, re, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get('C4VERIFY_DIR') or os.path.join(HERE, 'c4_verify_H'))
from lb4r import Inst, phase1_run, phase1_state, up_run, reach, any_output

def dense(sets, vals):
    m = 1 + max(g for S in sets for g in S)
    v = [[0] * m for _ in sets]
    for i, (S, V) in enumerate(zip(sets, vals)):
        for g, x in zip(S, V): v[i][g] = x
    return v

def optimal_classes(v, agents, goods):
    """every optimal matching of agents to their first or second choice among goods, as {agent: class}
    (0 first choice, 1 second, 2 unmatched): largest size, then most first choices"""
    top = {}
    for i in agents:
        r = sorted((g for g in goods if v[i][g] > 0), key=lambda g: -v[i][g])
        top[i] = r[:2]
    best, out = None, []
    for ch in itertools.product([0, 1, 2], repeat=len(agents)):
        gs = []
        ok = True
        for i, c in zip(agents, ch):
            if c < 2:
                if c >= len(top[i]): ok = False; break
                gs.append(top[i][c])
        if not ok or len(gs) != len(set(gs)): continue
        key = (sum(c < 2 for c in ch), sum(c == 0 for c in ch))
        if best is None or key > best: best, out = key, []
        if key == best: out.append(dict(zip(agents, ch)))
    return out

RANK = {17: lambda c: c, 18: lambda c: {1: 0, 0: 1, 2: 2}[c], 25: lambda c: c}

def taus(inst, v, rule):
    """every insertion sequence (PR #33's tau: positions among the unprocessed agents) the rule can produce"""
    n = inst.n
    static = optimal_classes(v, list(range(n)), list(range(inst.m))) if rule in (17, 18) else None
    out = set()
    def grow(tau, cls):
        run = phase1_run(inst, tau)
        I = [k for k, (_, _, t) in enumerate(run) if t == 'I']
        if len(I) <= len(tau): out.add(tuple(tau)); return
        k = I[len(tau)]
        done = [x for x, _, _ in run[:k]]
        U = [i for i in range(n) if i not in done]
        if rule == 25:
            taken = {f for _, f, _ in run[:k] if f is not None}
            G0 = [g for g in range(inst.m) if g not in taken]
            choices = {min(U, key=lambda x: (RANK[rule](c[x]), x)) for c in optimal_classes(v, U, G0)}
        else:
            choices = {min(U, key=lambda x: (RANK[rule](cls[x]), x))}
        for c in sorted(choices): grow(tau + [U.index(c)], cls)
    if static is None: grow([], None)
    else:
        for cls in static: grow([], cls)
    return sorted(out), static

def least_rotations(inst, tau, q=2):
    s0, _ = phase1_state(inst, tau); best = None
    for pol in ('shrink', 'envyFree', 'none'):
        s1, _ = up_run(inst, s0, pol)
        for d, lev in enumerate(reach(inst, s1, q)):
            if any(any_output(inst, s, conv) for s in lev for conv in ('bundle', 'base')):
                best = d if best is None else min(best, d); break
    return best

def lean_tau(tau, order):
    """adaptive.c's report (agents at the insertion steps, processing order) -> PR #33's tau"""
    out, done, it = [], set(), iter(tau)
    nxt = next(it, None)
    for x in order:
        if x == nxt: out.append(sorted(set(range(len(order))) - done).index(x)); nxt = next(it, None)
        done.add(x)
    return tuple(out)

def check(sets, vals, rule, verbose=True, tool_tau=None):
    """tie-robust? With tool_tau (adaptive.c's sequence, PR #33's form): also whether it is among the sequences
    derived here and needs two rotations in the model"""
    v = dense(sets, vals); inst = Inst(v)
    ts, static = taus(inst, v, rule)
    res = {t: least_rotations(inst, list(t)) for t in ts}
    robust = all(r is None or r >= 2 for r in res.values())
    if tool_tau is not None: return robust, tool_tau in res and (res[tool_tau] is None or res[tool_tau] >= 2)
    if verbose:
        if static is not None: print(f"    optimal matchings (class per agent: 0 first choice, 1 second, 2 unmatched): {[[c[i] for i in range(len(sets))] for c in static]}")
        for t, r in res.items(): print(f"    tau {list(t)}: fewest rotations {r if r is not None else '> 2'}")
    return robust

PROFILES = [   # (name, sets, vals): attempts/k4-adaptive-matching.md
    ('P1', [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [2, 3, 4, 8], [2, 7, 8, 4]]),
    ('P3', [[0, 1, 2, 5], [1, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 8, 6], [1, 4, 6, 8], [8, 2, 3, 4]]),
    ('T', [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [3, 5, 7, 6], [2, 3, 4, 8]]),
]

def main():
    args = sys.argv[1:]
    deep = next((a.split('=', 1)[1] for a in args if a.startswith('--deep=')), None)
    print('# adaptive_matching_ties.py', ' '.join(args), flush=True)
    if deep:
        tot = {}
        rule = None
        for line in open(deep):
            if line.startswith('# adaptive_run.py'): rule = int(re.search(r' -A(\d+)', line).group(1)); tot.setdefault(rule, [0] * 5); continue
            if not line.startswith('DEEP'): continue
            w = int(re.search(r' w=(\d+)', line).group(1))
            sets = json.loads(re.search(r'sets=(\[\[.*?\]\])', line).group(1)); vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', line).group(1))
            tau = [int(x) for x in line.split('tau=')[1].split()[0].split(',') if x]
            order = [int(x) for x in line.split('order=')[1].split('picks=')[0].split()]
            r, same = check(sets, vals, rule, verbose=False, tool_tau=lean_tau(tau, order))
            if not same: print(f"  MISMATCH (adaptive.c's sequence not derived here, or needs fewer than two in the model): {line.strip()}")
            if r: print(f"  rule {rule} tie-robust w={w} sets={sets} vals={vals}", flush=True)
            t = tot[rule]; t[0] += 1; t[1] += w; t[2] += r; t[3] += w * r; t[4] += not same
        for rule, (nl, wl, nr, wr, bad) in tot.items():
            print(f"rule {rule}: {nl} leaves (weight {wl}) need two rotations with adaptive.c's matching; on {nr} of them "
                  f"(weight {wr}) every optimal matching's sequence needs two (tie-robust); adaptive.c's own sequence is one "
                  f"of those derived here and needs two in the model on {nl - bad} of {nl}")
        return
    for name, sets, vals in PROFILES:
        print(f"{name}: sets={sets} vals={vals}")
        for rule in (17, 18, 25):
            print(f"  rule {rule}:")
            r = check(sets, vals, rule)
            print(f"  rule {rule}: {'tie-robust (every optimal matching needs two rotations)' if r else 'tie-dependent (some optimal matching needs at most one)'}")

if __name__ == '__main__':
    main()
