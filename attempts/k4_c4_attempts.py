"""Replay the smallest configurations of the failed approaches of k4/c4.md (attempts/k4-c4-*.md).

Each replay prints the Phase 1 state (after envy-free upgrades unless stated), checks the claim that fails with the
independent tracer k4/c4tools/c4trace.py (exact owner test by brute force over every completion), and, where the claim
is about a construction, lists by brute force over all n^m allocations (k4/lb4_brute.py, raw EFX0 definition, explicit
integers) the EFX0 allocations with at most one bundle of more than 2 goods, so it is the approach that fails, not K4.D.
Usage: python3 attempts/k4_c4_attempts.py [NAME ...]   (default: all)"""
import os, re, subprocess, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
K4 = os.path.join(HERE, '..', 'k4')
sys.path.insert(0, os.path.join(K4, 'c4tools')); sys.path.insert(0, K4)
from c4trace import *
import lb4_brute, lb4_run

def d2_solutions(sets, vals):
    return [X for X in lb4_brute.all_efx0(sets, vals) if sum(len(B) > 2 for B in X) <= 1]

def state(sets, vals, tau, mode=2):
    I = Inst(sets, vals)
    st = upgrades(initial_state(I, tau)[0], mode)
    r = max((i for i in range(I.n) if st.kind[i] == 'pick'), key=lambda i: st.pos[i])
    return I, st, r

def leader(st, x):
    return st.pos[x] == min(st.pos[j] for j in range(st.I.n) if st.blk[j] == st.blk[x])

def deficit(st, o):
    for e in range(0, 6):
        if owner_test(st, o, w1=False, extra=e): return e
    return None

def exposure_counting():
    ok = True
    # 1. an exposed 4-good agent that is not its block's leader (n = 3, m = 5)
    sets, vals, tau = [[0, 1, 3, 4], [2, 3, 4], [2, 3, 4]], [[3, 6, 8, 4], [2, 3, 4], [2, 3, 4]], [7, 4, 6]
    I, st, r = state(sets, vals, tau)
    E = exposed(st, r, st.base[r] | st.J)
    print('1. exposed non-leader:', sets, vals, 'insertion choices', tau); print(pretty(st))
    nl = [x for x in E if not leader(st, x)]
    print(f'   r = {r}, exposed {E}, not leaders {nl}, owner r valid: {owner_test(st, r, w1=False) is not None}')
    ok &= bool(nl) and all(len(I.R[x]) == 4 for x in nl)
    # 2. deficit 2 of owner r with a single exposed (flat) agent (n = 2, m = 5)
    sets, vals, tau = [[0, 2, 3, 4], [1, 2, 3, 4]], [[2, 7, 10, 4], [6, 3, 7, 5]], [2, 0]
    I, st, r = state(sets, vals, tau)
    dfc = deficit(st, r)
    print('2. deficit 2:', sets, vals, 'insertion choices', tau); print(pretty(st))
    print(f'   r = {r}, exposed {exposed(st, r, st.base[r] | st.J)}, deficit of r = {dfc}')
    ok &= dfc == 2
    # 3. the deficit sits in an earlier block (n = 3, m = 6)
    sets, vals, tau = [[0, 1, 2, 3], [2, 4, 5], [3, 4, 5]], [[3, 4, 2, 8], [2, 4, 3], [4, 2, 3]], [6, 3, 1]
    I, st, r = state(sets, vals, tau)
    E = exposed(st, r, st.base[r] | st.J)
    print('3. earlier-block deficit:', sets, vals, 'insertion choices', tau); print(pretty(st))
    print(f'   r = {r} (block {st.blk[r]}), exposed {E} in blocks {[st.blk[x] for x in E]}, '
          f'owner r valid: {owner_test(st, r, w1=False) is not None}, deficit {deficit(st, r)}')
    ok &= all(st.blk[x] != st.blk[r] for x in E) and owner_test(st, r, w1=False) is None
    return ok

def lbplus_rotation():
    # LB+'s bad case (no 4-good agent exposed) in which the 4-good r is exposed after LB+'s rotation (n = 3, m = 6)
    sets, vals, tau = [[0, 1, 2, 5], [2, 3, 4, 5], [3, 4, 5]], [[2, 4, 8, 5], [8, 3, 4, 6], [2, 3, 4]], [5, 3, 7]
    I, st, r = state(sets, vals, tau)
    W = st.base[r] | st.J
    E = exposed(st, r, W)
    ks = min((i for i in range(I.n) if st.blk[i] == st.blk[r]), key=lambda i: st.pos[i])
    ch = [c for c in chains_from(st, ks) if c[-1] == r][0]
    ns = rotate(st, ch, frozenset(I.ord[ks][1:3]))
    ok_k = (ns.omega() <= 0 and owner_test_none(ns)) or owner_test(ns, ks, w1=True)
    print('LB+ rotation, 4-good r:', sets, vals, 'insertion choices', tau); print(pretty(st))
    print(f'   r = {r}, exposed {E} (all 3-good), owner r valid: {owner_test(st, r, w1=False) is not None}; '
          f'k* = {ks}, chain {ch}')
    print(pretty(ns))
    E2 = exposed(ns, ks, ns.base[ks] | ns.J)
    print(f'   after the rotation: exposed {E2}, owner k* valid (needs from bundle): {bool(ok_k)}')
    fixes = search(st, 1, w1=True)
    print(f'   single rotations that work: {[(p, o) for p, o, X in fixes]}')
    sols = d2_solutions(sets, vals)
    print(f'   brute force: {len(sols)} EFX0 allocations with at most one large bundle, e.g. {sols[:2]}')
    return E2 == [r] and not ok_k and len(sols) > 0

def lb4c(opts, m, sets):
    lb4_run.build()
    p = subprocess.run([lb4_run.BIN] + opts.split() + ['-f1'], input=lb4_run.encode(sets, m, False),
                       capture_output=True, text=True, check=True)
    kv = dict(zip(p.stdout.split()[0:22:2], map(int, p.stdout.split()[1:22:2])))
    fail = [l for l in p.stderr.split('\n') if l.startswith('FAIL')]
    return kv, fail

def one_rotation():
    ok = True
    for what, opts, m, sets in [
        ('two 4-good agents, all three policies, every owner, one rotation', '-i1 -u3 -o0 -r1 -w1 -c1', 6,
         [[0, 1, 2, 5], [2, 3, 4, 5], [3, 4, 5]]),
        ('one 4-good agent, envy-free upgrades, owner r only, one rotation', '-i1 -u2 -o2 -r1 -w0 -c0', 6,
         [[0, 2, 4, 5], [1, 3, 5], [3, 4, 5]])]:
        kv, fail = lb4c(opts, m, sets)
        print(f'{what} (lb4.c {opts}): core m={m} sets={sets}: {kv["fails"]} of {kv["total"]} (run, profile) pairs fail')
        if not fail: ok = False; continue
        print('  ', fail[0])
        vals = json.loads(re.search(r'vals=(\[\[.*?\]\])', fail[0]).group(1))
        sols = d2_solutions(sets, vals)
        print(f'   brute force: {len(sols)} EFX0 allocations with at most one large bundle, e.g. {sols[:2]}')
        ok &= kv['fails'] > 0 and len(sols) > 0
    # the same with one more rotation passes
    kv, _ = lb4c('-i1 -u2 -o0 -r2 -w1 -c1', 6, [[0, 1, 2, 5], [2, 3, 4, 5], [3, 4, 5]])
    print(f'   with two rotations (-i1 -u2 -o0 -r2 -w1 -c1) the first core has {kv["fails"]} failures')
    return ok and kv['fails'] == 0

def pareto_moves():
    # a dead end of the Pareto-improving move graph (upgrades and rotations in which the rotated agent gains)
    sets, vals, tau = [[0, 1, 2, 3], [0, 1, 4, 5], [2, 3, 4, 5]], [[8, 6, 4, 1], [4, 2, 8, 5], [4, 6, 8, 3]], [2, 6, 0]
    I = Inst(sets, vals)
    st = initial_state(I, tau)[0]
    print('Pareto moves:', sets, vals, 'insertion choices', tau, '(no upgrades in Phase 1)'); print(pretty(st))
    seen = {}; frontier = [(st, ())]; dead = []; success = []
    while frontier:
        s, path = frontier.pop()
        key = (tuple(s.base), tuple(s.kind))
        if key in seen: continue
        good = try_owners(s) is not None
        seen[key] = good
        if good: success.append(path); continue
        moves = list(pi_moves(s))
        if not moves: dead.append((s, path))
        for dsc, ns in moves: frontier.append((ns, path + (dsc,)))
    print(f'   reachable states {len(seen)}, dead ends {len(dead)}, states with a valid owner {len(success)}')
    if dead:
        s, path = dead[0]
        print('   a dead end, reached by', path); print(pretty(s))
    return len(dead) > 0 and len(success) > 0

def owner_last_():
    sets, vals, tau = [[0, 2, 6, 7], [1, 4, 6, 7], [3, 5, 6, 7]], [[6, 3, 5, 7], [5, 3, 6, 7], [3, 8, 4, 10]], [2, 6, 5]
    I = Inst(sets, vals)
    print('Owner last:', sets, vals, 'insertion choices', tau)
    anyok = False
    for o in range(I.n):
        agents = [i for i in range(I.n) if i != o]
        Y, pos, blk, G, nopts = phase1_sub(I, agents, tau)
        avail = sorted(G & I.R[o])
        for rr in range(len(avail), -1, -1):
            for O in itertools.combinations(avail, rr):
                st = owner_last(I, o, tau, O)
                if not st.valid(): continue
                if (len(st.base[o]) <= 2 and st.omega() <= 0 and owner_test_none(st)) or owner_test(st, o):
                    anyok = True; print('   works with owner', o, O)
        print(f'   owner {o} last: others pick {Y}, left for o {avail}')
    sols = d2_solutions(sets, vals)
    print(f'   no owner works: {not anyok}; brute force: {len(sols)} EFX0 allocations with at most one large bundle, '
          f'e.g. {sols[:2]}')
    return not anyok and len(sols) > 0

def gadget_stacking():
    # a core where LB4r (index insertion) needs two rotations; two copies joined by a shared private junk good need one
    sets, vals = [[0, 1, 4, 5], [2, 3, 4, 5], [2, 3, 4, 5]], [[1, 4, 6, 8], [3, 5, 7, 6], [2, 3, 4, 8]]
    def run(S, V, M, opts):
        lb4_run.build()
        inp = f"{len(S)} {M}\n" + ''.join(f"{len(s)} {' '.join(map(str, s))} 1\n{' '.join(map(str, v))}\n" for s, v in zip(S, V))
        p = subprocess.run([lb4_run.BIN] + opts.split(), input=inp, capture_output=True, text=True, check=True)
        return int(p.stdout.split()[7])
    one = [run(sets, vals, 6, f'-i0 -u3 -r{k} -w1 -c1') for k in (1, 2)]
    # two copies: copy 2's goods are 6..11, except that its good 1 (private to its agent 0) is copy 1's good 0
    mp = {0: 6, 1: 0, 2: 7, 3: 8, 4: 9, 5: 10}
    S2 = sets + [[mp[g] for g in s] for s in sets]; V2 = vals + vals
    two = [run(S2, V2, 11, f'-i0 -u3 -r{k} -w1 -c1') for k in (1, 2)]
    print(f'Gadget stacking: one copy fails with 1 rotation: {one[0] == 1}, passes with 2: {one[1] == 0}; '
          f'two copies (n = 6) fail with 1 rotation: {two[0] == 1}')
    return one == [1, 0] and two[0] == 0

def phase1_order(I, order):
    """Phase 1 with a given processing order (any P-step order, not only LB's key); asserts that each step is legal:
    a P-step whenever some unprocessed agent has lost a good, an insertion step (a new block) otherwise"""
    G = set(range(I.m)); Y = [None] * I.n; pos = [0] * I.n; blk = [0] * I.n; b = -1; done = set()
    for step, i in enumerate(order):
        lost = [x for x in range(I.n) if x not in done and not I.R[x] <= G]
        assert (i in lost) if lost else True, f'step {step}: agent {i} is not a legal P-step choice'
        if not lost: b += 1
        Y[i] = next((g for g in I.ord[i] if g in G), None)
        if Y[i] is not None: G.discard(Y[i])
        done.add(i); pos[i] = step; blk[i] = b
    base = [frozenset([y]) if y is not None else frozenset() for y in Y]
    return State(I, base, ['pick'] * I.n, frozenset(G), pos, blk, Y)

def g2_other_runs():
    # k4/c4.md §6.1 item 4: for runs of Phase 1 other than lb4.c's (a P-step order that is not LB's key), LB+'s rotation
    # can leave k* invalid with a single 4-good agent (review of PR #33, finding F4; n = 4, m = 7)
    sets, vals = [[0, 2, 5], [1, 5, 6], [2, 3, 4, 6], [3, 4, 6]], [[2, 3, 4], [2, 4, 3], [8, 4, 3, 6], [2, 3, 4]]
    I = Inst(sets, vals)
    st = upgrades(phase1_order(I, [3, 1, 0, 2]), 2)
    print('G2 in other runs: agent 0 is processed before agent 2 in a P-step (LB\'s key would take agent 2)'); print(pretty(st))
    r = max((i for i in range(I.n) if st.kind[i] == 'pick'), key=lambda i: st.pos[i])
    E = exposed(st, r, st.base[r] | st.J)
    ks = min((i for i in range(I.n) if st.blk[i] == st.blk[r]), key=lambda i: st.pos[i])
    chs = [c for c in chains_from(st, ks)]
    print(f'   r = {r}, exposed {E}, owner r valid: {owner_test(st, r, w1=False) is not None}; k* = {ks}, chains {chs}')
    ns = rotate(st, chs[0], frozenset(I.ord[ks][1:3]))
    print(pretty(ns))
    kval = ns.omega() <= 0 and owner_test_none(ns) or owner_test(ns, ks, w1=True)
    out = [g for g in ns.J if g not in I.R[r]]          # k*'s bundle holds O and, as omega' = 1, a junk good outside R_r
    thr = I.val(r, ns.base[ks]) > I.val(r, ns.base[r]) and len(out) > 0
    print(f'   after LB+\'s rotation: omega {ns.omega()}; r values O = {sorted(ns.base[ks])} at {I.val(r, ns.base[ks])} > '
          f'{I.val(r, ns.base[r])}, its base, and junk outside R_r is {out}: r is threatened by every bundle of k*: {thr}; '
          f'k* a valid owner: {bool(kval)}')
    fixes = [(p, o) for p, o, X in search(st, 1, w1=True)]
    print(f'   single rotations that work: {fixes}')
    return E == [ks] and len(chs) == 1 and chs[0][-1] == r and not kval and thr and any(p[0][0][0] == 0 and p[0][1] == (0,) for p, o in fixes)

ALL = {'exposure-counting': exposure_counting, 'lbplus-rotation': lbplus_rotation, 'one-rotation': one_rotation,
       'pareto-moves': pareto_moves, 'owner-last': owner_last_, 'gadget-stacking': gadget_stacking,
       'g2-other-runs': g2_other_runs}

if __name__ == '__main__':
    names = sys.argv[1:] or list(ALL)
    res = {nm: ALL[nm]() for nm in names}
    print('\n' + '\n'.join(f'{nm}: {"reproduced" if v else "NOT reproduced"}' for nm, v in res.items()))
    sys.exit(0 if all(res.values()) else 1)
