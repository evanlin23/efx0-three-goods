"""Step-by-step trace of algorithm K3ALG on small instances, for the examples of paper/k3/long.tex.

Every intermediate state printed here is recomputed with the methods of the repository's literal transcription of the
Lean program (`k3/k3algo.py`: class `LB`, functions `r1_step`, `profile_of`), in the order in which `mirror` (and the
Lean definition `EFX.K3.algoSpec`) calls them. The script then checks that
  - the allocation assembled from the trace equals `mirror`'s and `fast`'s outputs (`k3/k3algo.py`), and
  - it is EFX0 by the raw definition, twice: `raw_efx0_naive` (three nested loops over agents, agents and removed
    goods) and an independent brute-force check written below (`efx0_brute`), which recomputes every bundle value
    from scratch for every removed good.
It also checks the side claims the paper makes about each example (see `CLAIMS`).

Usage: python3 paper/k3/examples/trace.py > paper/k3/examples/trace_output.txt
       (prints the traces and the checks; exit status 1 if any check fails)
"""
import os, sys, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'k3'))
import k3algo
from k3algo import LB, r1_step, profile_of, mirror, fast, raw_efx0_naive, _erase

def efx0_brute(n, m, v, X):
    """EFX0 from the definition: for all i != j and every h in X_j, v_i(X_i) >= v_i(X_j minus {h})."""
    bundle = lambda j: [g for g in range(m) if X[g] == j]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    bad = []
    for i in range(n):
        for j in range(n):
            if i == j: continue
            for h in bundle(j):
                rest = [g for g in bundle(j) if g != h]
                if val(i, rest) > val(i, bundle(i)):
                    bad.append((i, j, h, val(i, rest), val(i, bundle(i))))
    return bad

def gname(g): return 'g%d' % g
def gs(S): return '{' + ', '.join(gname(g) for g in sorted(S)) + '}' if S else '{}'

def trace(name, n, m, v, out):
    p = lambda *a: print(*a, file=out)
    p('=' * 100); p('Example', name, ': n = %d, m = %d' % (n, m))
    for i in range(n):
        p('  agent %d values ' % i + ', '.join('%s: %d' % (gname(g), x) for g, x in sorted(v[i].items(), key=lambda t: t[0])))
    # ---- Stage R (as `mirror`)
    agents, goods, peeled = list(range(n)), list(range(m)), {}
    p('Stage R:')
    while True:
        if len(agents) <= 1:
            p('  one agent left:', agents, '-> it takes all remaining goods', gs(goods)); return None
        if not goods:
            p('  no goods left'); return None
        step = None
        for i in agents:
            st = r1_step(v, goods, i)
            f = lambda g: v[i].get(g, 0)
            fav = k3algo.favorite(f, goods)
            rest = sum(f(g) for g in _erase(goods, fav))
            p('  agent %d: favourite %s worth %d, rest worth %d -> %s' % (i, gname(fav), f(fav), rest,
              'R1 fails' if st is None else ('peel with nothing' if st[0] == 'empty' else 'peel with ' + gname(st[1]))))
            if st is not None: step = (i, st); break
        if step is None: break
        i, st = step
        agents = _erase(agents, i)
        if st[0] == 'good': peeled[st[1]] = i; goods = _erase(goods, st[1])
        p('  -> agent %d peeled' % i + (' with ' + gname(st[1]) if st[0] == 'good' else ' with nothing'))
    p('  Stage R stops: agents', agents, 'goods', gs(goods))
    # ---- Stage L
    P = profile_of(v, n, goods)
    lb = LB(P)
    for i in agents: p('  L1: agent %d ranks a=%s > b=%s > c=%s' % (i, gname(lb.a(i)), gname(lb.b(i)), gname(lb.c(i))))
    order = lb.r1_order(len(agents), agents, goods)
    Y = lb.phase1(order, goods)
    blk = lb.blk_aux(order, goods)
    pool = list(goods)
    p('Phase 1 (order %s):' % order)
    for i in order:
        full = lb.full(pool, i)
        left = [g for g in P[i] if g in pool]
        y = lb.fav(pool, i)
        p('  agent %d: %s left of its goods, %s step, block %d, picks %s%s' % (i, gs(left), 'insertion' if full else 'R1',
          blk(i), gname(y) if y is not None else 'nothing',
          '' if y is None else ' (its %s)' % 'abc'[lb.rank(i, y)]))
        pool = lb.remove_pick(pool, y)
    J0 = lb.junk0(agents, Y, goods)
    p('  unpicked after Phase 1: %s' % gs(J0))
    # upgrades, as LB.upgrades, with the order of upgrades
    up, J = [], list(J0)
    for _ in range(len(agents)):
        k = next((k for k in agents if lb.can_up(agents, up, Y, J, k)), None)
        if k is None: break
        p('  upgrade: agent %d (pick %s = b, c = %s junk, b not needed alone) gets %s' % (k, gname(Y(k)), gname(lb.c(k)), gname(lb.c(k))))
        up = [k] + up; J = _erase(J, lb.c(k))
    assert up == lb.lb_up(agents, goods, Y)
    X, tag = state_and_complete(lb, agents, goods, order, Y, up, blk, p)
    Xfull = [peeled[g] if g in peeled else X(g) for g in range(m)]
    Xm, info = mirror(n, m, v)
    Xf, _ = fast(n, m, v)
    ok = True
    p('Result: branch %s' % tag)
    for j in range(n):
        B = [g for g in range(m) if Xfull[g] == j]
        p('  X_%d = %s   (v_%d(X_%d) = %d)' % (j, gs(B), j, j, sum(v[j].get(g, 0) for g in B)))
    p('  equals mirror: %s; equals fast: %s; mirror branch: %s' % (Xfull == Xm, Xfull == Xf, info['branch']))
    ok &= (Xfull == Xm) and (Xfull == Xf) and info['branch'] == tag
    e1 = raw_efx0_naive(n, m, v, Xfull); e2 = efx0_brute(n, m, v, Xfull)
    p('  EFX0 (raw_efx0_naive): %s; EFX0 (efx0_brute): %s' % (e1, not e2))
    ok &= e1 and not e2
    return ok, Xfull

def describe_state(lb, agents, goods, Y, up, p, label):
    J = lb.junk_list(agents, up, Y, goods)
    NA = set()
    p('%s:' % label)
    for i in agents:
        if i in up:
            p('  agent %d: upgraded, base {%s, %s}' % (i, gname(lb.b(i)), gname(lb.c(i)))); continue
        Ni = [g for g in P_of(lb, i) if lb.prefers(Y, i, g)]
        NA |= set(Ni)
    for i in agents:
        if i in up: continue
        Ni = [g for g in P_of(lb, i) if lb.prefers(Y, i, g)]
        fr = lb.frozenB(agents, up, Y, i)
        p('  agent %d: pick %s, needs N = %s, %s, cap %d' % (i, gname(Y(i)) if Y(i) is not None else 'none', gs(Ni),
          'frozen' if fr else 'terminal', lb.cap(agents, up, Y, i)))
    S = lb.slot_sum(agents, up, Y)
    p('  J = %s (|J| = %d), NA = %s, S = %d, omega = |J| - S = %d' % (gs(J), len(J), gs(NA), S, len(J) - S))
    return J, NA, S

def P_of(lb, i): return lb.P[i]

def exposed_report(lb, agents, up, Y, goods, w, J, p):
    E = lb.exposed_l(agents, up, Y, goods, w)
    for x in E:
        pi = [g for g in (lb.b(x), lb.c(x)) if g in J]
        p('  exposed for %d: agent %d (pick a = %s; b = %s, c = %s), pi = %s' % (w, x, gname(lb.a(x)), gname(lb.b(x)),
          gname(lb.c(x)), gs(pi)))
    mt = lb.meet(J, E)
    H = lb.hit_set(J, E)
    p('  E = %s, meet = %s, HitSet = [%s]' % (E, mt, ', '.join(gname(g) for g in H)))
    return E, H

def state_and_complete(lb, agents, goods, order, Y, up, blk, p):
    J, NA, S = describe_state(lb, agents, goods, Y, up, p, 'After Phase 1 and the upgrades (U = %s)' % sorted(up))
    d = 0
    if len(J) <= S:
        p('  |J| <= S: complete without owner')
        X = lb.complete(agents, up, Y, goods, None, [], d); show_fill(lb, agents, up, Y, goods, None, [], p)
        return X, 'noowner'
    r = lb.last_out(up, order)
    p('Owner test: r = %d (block %d), S - cap(r) = %d' % (r, blk(r), S - lb.cap(agents, up, Y, r)))
    E, H = exposed_report(lb, agents, up, Y, goods, r, J, p)
    Sr = S - lb.cap(agents, up, Y, r)
    if len(H) <= Sr:
        p('  |H| = %d <= %d: owner r = %d' % (len(H), Sr, r))
        X = lb.complete(agents, up, Y, goods, r, H, d); show_fill(lb, agents, up, Y, goods, r, H, p)
        return X, 'owner_r'
    p('  |H| = %d > %d: r fails' % (len(H), Sr))
    k = lb.kstar(agents, up, Y, goods, blk, r)
    ch = lb.chain_from(agents, up, Y, k, lb.after(order, k))
    p('Rotation: k* = %d, need chain %s' % (k, ' -> '.join(str(x) for x in [k] + ch)))
    Y2 = lb.rot_picks(Y, k, ch)
    for x in [k] + ch:
        p('  agent %d: pick %s -> %s' % (x, gname(Y(x)) if Y(x) is not None else 'none', gname(Y2(x))))
    up2 = [k] + up
    J2, NA2, S2 = describe_state(lb, agents, goods, Y2, up2, p, 'After the rotation (U = %s)' % sorted(up2))
    if len(J2) <= S2:
        p('  |J\'| <= S\': complete without owner')
        X = lb.complete(agents, up2, Y2, goods, None, [], d); show_fill(lb, agents, up2, Y2, goods, None, [], p)
        return X, 'rot_noowner'
    E2, H2 = exposed_report(lb, agents, up2, Y2, goods, k, J2, p)
    p('  owner k* = %d, HitSet [%s] (slots %d)' % (k, ', '.join(gname(g) for g in H2), S2))
    X = lb.complete(agents, up2, Y2, goods, k, H2, d); show_fill(lb, agents, up2, Y2, goods, k, H2, p)
    return X, 'rot_owner_k'

def show_fill(lb, agents, up, Y, goods, o, H, p):
    J = lb.junk_list(agents, up, Y, goods)
    L = list(H) + [g for g in J if g not in H]
    s = lb.slots_except(lambda k: lb.cap(agents, up, Y, k), o)
    p('  placement list L = [%s]; slots (owner excluded): %s' % (', '.join(gname(g) for g in L),
      {k: s(k) for k in agents if s(k) > 0}))

EXAMPLES = {}
CLAIMS = []

def main():
    ok = True
    for name, (n, m, v) in EXAMPLES.items():
        r = trace(name, n, m, v, sys.stdout)
        ok &= r[0]
    for desc, fn in CLAIMS:
        res = fn()
        print('CLAIM %-90s %s' % (desc, 'OK' if res else 'FAILED'))
        ok &= res
    print('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED')
    return 0 if ok else 1

def inst(tbl):
    """An instance from a list of rows {good: value}."""
    n = len(tbl); m = 1 + max(g for row in tbl for g in row)
    return n, m, [dict(row) for row in tbl]

def from_table(tbl):
    """An instance from the Lean `mkInst` table: tbl[i][g] = v_i(g)."""
    n, m = len(tbl), max(len(r) for r in tbl)
    return n, m, [{g: x for g, x in enumerate(r) if x > 0} for r in tbl]

# ------------------------------------------------------------------------------------------------------------------
# The examples of the paper
# ------------------------------------------------------------------------------------------------------------------
# Example 2 of long.tex (running example, owner r): five agents, nine goods; agent 4 values only g5.
EX1 = (5, 9, [{2: 6, 4: 5, 6: 2}, {6: 5, 7: 4, 0: 3}, {2: 9, 1: 7, 3: 5}, {2: 9, 8: 8, 1: 7}, {5: 6}])
# Example 3 of long.tex (rotation, owner k*): four agents, eight goods.
EX2 = (4, 8, [{2: 8, 5: 7, 0: 3}, {4: 8, 6: 6, 1: 4}, {4: 9, 7: 8, 3: 3}, {4: 9, 7: 6, 0: 4}])
# Remark 1 (a repeated good), after the size proposition: HitSet lists a good twice, a slot stays empty, the owner gets omega + 3 goods.
EXDUP = (4, 9, [{1: 4, 0: 3, 2: 2}, {3: 4, 0: 3, 4: 2}, {5: 4, 0: 3, 6: 2}, {7: 4, 0: 3, 8: 2}])
EXAMPLES['Example 2 (owner r)'] = EX1
EXAMPLES['Example 3 (rotation, owner k*)'] = EX2
EXAMPLES['Remark 1 (repeated good in HitSet)'] = EXDUP
# the Lean examples of lean/EFX/K3Examples.lean (outputs checked there by `decide`)
EXAMPLES['Lean peelOwner'] = from_table([[0, 0, 84, 0, 73, 54], [0, 87, 0, 0, 0, 0], [0, 0, 83, 44, 92, 0]])
EXAMPLES['Lean rotOwner'] = from_table([[2, 5, 4, 0, 0, 0], [0, 3, 2, 3, 0, 0], [0, 3, 2, 3, 0, 0]])
EXAMPLES['Lean rot'] = from_table([[0, 2, 0, 2, 2], [0, 3, 3, 0, 2], [0, 2, 2, 0, 2]])

def alloc(m, bundles):
    X = [None] * m
    for j, B in bundles.items():
        for g in B: X[g] = j
    assert None not in X
    return X

def efx_brute(n, m, v, X):
    """Ordinary EFX: only goods h with v_i(h) > 0 may be removed."""
    bundle = lambda j: [g for g in range(m) if X[g] == j]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    return all(val(i, [g for g in bundle(j) if g != h]) <= val(i, bundle(i))
               for i in range(n) for j in range(n) if i != j for h in bundle(j) if v[i].get(h, 0) > 0)

def case_of(v, i, X, m):
    """The cases of Lemma 2 of long.tex (ledger L5) that agent i (three relevant goods) satisfies in X."""
    a, b, c = sorted(v[i], key=lambda g: (-v[i][g], g))
    size = lambda g: sum(1 for h in range(m) if X[h] == X[g])
    alone = lambda g: size(g) == 1
    holds = lambda g: X[g] == i
    out = []
    if holds(a) and (holds(b) or holds(c) or X[b] != X[c] or size(b) < 3): out.append('T')
    if holds(b) and holds(c): out.append('P')
    if holds(b) and alone(a): out.append('B')
    if holds(c) and alone(a) and alone(b): out.append('C')
    if alone(a) and alone(b) and alone(c): out.append('E')
    return out

def omega_formula(ex):
    """|J| - S = m - 2n + |NA| on the Stage-L instance (size proposition), before and after a rotation."""
    n, m, v = ex
    agents, goods = list(range(n)), list(range(m))
    while True:
        st = next(((i, s) for i in agents for s in [r1_step(v, goods, i)] if s is not None), None) if len(agents) > 1 and goods else None
        if st is None: break
        i, s = st; agents = _erase(agents, i)
        if s[0] == 'good': goods = _erase(goods, s[1])
    lb = LB(profile_of(v, n, goods)); order = lb.r1_order(len(agents), agents, goods)
    Y = lb.phase1(order, goods); up = lb.lb_up(agents, goods, Y)
    def check(Y, up):
        J = lb.junk_list(agents, up, Y, goods); S = lb.slot_sum(agents, up, Y)
        NA = {g for i in agents if i not in up for g in lb.P[i] if lb.prefers(Y, i, g)}
        return len(J) - S == len(goods) - 2 * len(agents) + len(NA)
    ok = check(Y, up)
    J = lb.junk_list(agents, up, Y, goods)
    if len(J) > lb.slot_sum(agents, up, Y):
        r = lb.last_out(up, order); blk = lb.blk_aux(order, goods)
        H = lb.hit_set(J, lb.exposed_l(agents, up, Y, goods, r))
        if len(H) > lb.slot_sum(agents, up, Y) - lb.cap(agents, up, Y, r):
            k = lb.kstar(agents, up, Y, goods, blk, r)
            Y2 = lb.rot_picks(Y, k, lb.chain_from(agents, up, Y, k, lb.after(order, k)))
            ok &= check(Y2, [k] + up)
    return ok

def claim_intro():
    # Example 1 (Section 1): a = g0, b = g1, c = g2; agent 0 values a, b at 3, 2; agent 1 values only c.
    v = [{0: 3, 1: 2}, {2: 1}]
    X = alloc(3, {0: [1], 1: [0, 2]}); Z = alloc(3, {0: [0], 1: [1, 2]})
    return efx_brute(2, 3, v, X) and not raw_efx0_naive(2, 3, v, X) and raw_efx0_naive(2, 3, v, Z)

def claim_ex1_wrong_slot():
    # Example 2: filling agent 3's slot with g0 instead of g4 gives the owner {g4, g6, g7}: EFX but not EFX0
    n, m, v = EX1
    X = alloc(m, {0: [2], 1: [6, 4, 7], 2: [1, 3], 3: [8, 0], 4: [5]})
    bad = efx0_brute(n, m, v, X)
    return efx_brute(n, m, v, X) and bad and all(t[0] == 0 and t[1] == 1 for t in bad)

def claim_ex1_cases():
    n, m, v = EX1
    X, _ = mirror(n, m, v)
    return [case_of(v, i, X, m) for i in range(4)] == [['T'], ['T', 'P'], ['P', 'B'], ['B']]

def claim_ex2_r_fails():
    # Example 3: every completion with owner r = 3 (agent 0's one slot takes one junk good, agent 3 the rest) fails
    n, m, v = EX2
    J = [1, 3, 5, 6]
    for s in J + [None]:                              # None: agent 0's slot left empty
        slot = [] if s is None else [s]
        X = alloc(m, {0: [2] + slot, 1: [4], 2: [7], 3: [0] + [g for g in J if g != s]})
        if raw_efx0_naive(n, m, v, X): return False
    return True

def claim_ex2_cases():
    n, m, v = EX2
    X, _ = mirror(n, m, v)
    return [case_of(v, i, X, m) for i in range(4)] == [['T'], ['P', 'B'], ['T'], ['P', 'B']]

def claim_dup():
    n, m, v = EXDUP
    X, info = mirror(n, m, v)
    sizes = [sum(1 for g in range(m) if X[g] == j) for j in range(n)]
    return info['branch'] == 'owner_r' and sizes == [2, 1, 2, 4] and raw_efx0_naive(n, m, v, X)

def largest_threats(ex):
    """For each agent i of the output: (v_i(X_i), max_{j != i} theta_i(X_j), the bundles attaining it)."""
    n, m, v = ex
    X, _ = mirror(n, m, v)
    bundle = lambda j: [g for g in range(m) if X[g] == j]
    val = lambda i, S: sum(v[i].get(g, 0) for g in S)
    def theta(i, B):
        return max((val(i, [g for g in B if g != h]) for h in B), default=0)
    out = []
    for i in range(n):
        th = {j: theta(i, bundle(j)) for j in range(n) if j != i}
        t = max(th.values())
        out.append((val(i, bundle(i)), t, sorted(j for j in th if th[j] == t) if t > 0 else []))
    return out

def claim_ex1_threats():
    # Table 3: own values 6, 12, 12, 8, 6; largest threats 5 (from X_3), 0, 0, 7 (from X_2), 0
    return largest_threats(EX1) == [(6, 5, [3]), (12, 0, []), (12, 0, []), (8, 7, [2]), (6, 0, [])]

def claim_ex2_threats():
    # Table 4: own values 15, 10, 9, 10; largest threats 3 (from X_3), 0, 8 (from X_3), 0
    return largest_threats(EX2) == [(15, 3, [3]), (10, 0, []), (9, 8, [3]), (10, 0, [])]

def claim_omega():
    return all(omega_formula(ex) for ex in EXAMPLES.values())

CLAIMS += [
    ('Example 1: ({g1}, {g0, g2}) is EFX, not EFX0; ({g0}, {g1, g2}) is EFX0', claim_intro),
    ('Example 2: slot of agent 3 filled with g0 gives an EFX, non-EFX0 allocation (agent 0 vs owner 1)', claim_ex1_wrong_slot),
    ('Example 2 (Table 3): cases of Lemma 2 (ledger L5) met by agents 0-3 in the output: T; T, P; P, B; B', claim_ex1_cases),
    ('Example 2 (Table 3): own values and largest threats 6/5 (X_3), 12/0, 12/0, 8/7 (X_2), 6/0', claim_ex1_threats),
    ('Example 3: every completion with owner r = 3 violates EFX0 (slot filled or empty)', claim_ex2_r_fails),
    ('Example 3 (Table 4): own values and largest threats 15/3 (X_3), 10/0, 9/8 (X_3), 10/0', claim_ex2_threats),
    ('Example 3 (Table 4): cases of Lemma 2 (ledger L5) met by agents 0-3 in the output: T; P, B; T; P, B', claim_ex2_cases),
    ('Remark 1: owner r = 3 gets 4 = omega + 3 goods, agent 1 keeps an empty slot, output EFX0', claim_dup),
    ('omega = m - 2n + |NA| (Stage-L n, m) in every example, before and after a rotation', claim_omega),
]

if __name__ == '__main__':
    sys.exit(main())
