"""Proposition H3 (k4/p3.md section 2.3), step by step on every reachable state: the structural steps of the proof,
checked on every valid state that LB4r reaches from Phase 1 (index insertion) of H3_t (variant A of k4/p3/ht3.py) with
at most Q nested rotations, using the independent tracer k4/c4tools/c4trace.py (Phase 1, validity, needs, need chains,
rotations, slots with a rotated one-good base given a slot). Mirrors k4/c4_chain.py's `reach` for H_t, with two x's
per gadget. Checks: the Phase 1 state (picks, junk, the x's frozen, no upgrade under policies 1 and 2); in every state,
l keeps g_1 and needs nothing, every need of an agent is an a of its own gadget, every need chain lies inside one
gadget; per-gadget counts (slot places minus forced agents): untouched -1, touched <= +1, l <= 0; at most d gadgets
touched after d rotations. Prints the largest total per depth and the proof's bound 2d - t.
    python3 k4/p3/ht3_reach.py T Q
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'c4tools')); sys.path.insert(0, HERE)
import c4trace as T
import ht3

def reach(t, Q):
    sets, vals, m = ht3.build(t, 'A')
    I = T.Inst(sets, vals); n = I.n
    G = 3                                                                    # agents per gadget: x_j1, x_j2, y_j
    gad = [None] + [(i - 1) // G for i in range(1, n)]
    isx = lambda i: i > 0 and (i - 1) % G != G - 1
    A = [frozenset(sets[1 + G * j + G - 1][:2]) for j in range(t)]          # the a's of gadget j
    g1 = sets[0][0]; u, u2 = sets[0][2], sets[0][3]
    st0 = T.initial_state(I, [])[0]
    ok = st0.Y[0] == g1
    for j in range(t):
        for i in range(2):
            x = 1 + G * j + i; ok &= st0.Y[x] == sets[x][0]
        ok &= st0.Y[1 + G * j + 2] == sets[1 + G * j + 2][2]
    Jexp = {u, u2} | {g for j in range(t) for i in range(2) for g in sets[1 + G * j + i][1:3]}
    ok &= set(st0.J) == Jexp
    fr0 = st0.frozen()
    ok &= all(fr0[i] == isx(i) for i in range(n))
    ok &= all(T.upgrades(st0, mode).base == st0.base for mode in (1, 2))
    print(f'  Phase 1 as in the proof (picks, junk, the x\'s frozen, no upgrade under policies 1 and 2): {ok}; '
          f'omega = {st0.omega()} (proof: >= t + 1 = {t + 1})', flush=True)
    base0 = list(st0.base)
    key = lambda s: (tuple(s.base), tuple(s.kind))
    seen = {key(st0): 0}; level = [st0]; bad = []; worst = {}
    def audit(s, d):
        if s.base[0] != frozenset([g1]) or s.kind[0] != 'pick' or s.needs(0): bad.append(('l', d)); return
        for i in range(1, n):
            if not s.needs(i) <= A[gad[i]]: bad.append(('needs', i, d)); return
        fr = s.frozen()
        for k in range(n):
            if fr[k]:
                for ch in T.chains_from(s, k):
                    if len({gad[x] for x in ch}) != 1: bad.append(('chain', ch, d)); return
        if s.omega() < t + 1: bad.append(('omega', d)); return
        cap = s.caps(rot_slot=True)
        tot = cap[0] - (1 if {u, u2} <= s.J else 0)
        if tot > 0: bad.append(('l count', d)); return
        touched = 0
        for j in range(t):
            ag = range(1 + G * j, 1 + G * (j + 1))
            forced = sum(1 for x in ag if isx(x) and s.kind[x] == 'pick' and s.base[x] == frozenset([sets[x][0]])
                         and set(sets[x][1:3]) <= s.J)
            c = sum(cap[x] for x in ag) - forced
            if any(s.base[x] != base0[x] or s.kind[x] != 'pick' for x in ag):
                touched += 1
                if c > 1: bad.append(('touched count', j, c, d)); return
            elif c != -1: bad.append(('untouched count', j, c, d)); return
            tot += c
        if touched > d: bad.append(('touched', touched, d)); return
        worst[d] = max(worst.get(d, -99), tot)
    audit(st0, 0)
    for d in range(1, Q + 1):
        nxt = []
        for s in level:
            fr = s.frozen()
            for k in range(n):
                if not fr[k]: continue
                for ch in T.chains_from(s, k):
                    for O in T.rot_options(s, ch):
                        ns = T.rotate(s, ch, O)
                        if not ns.valid() or key(ns) in seen: continue
                        seen[key(ns)] = d; nxt.append(ns); audit(ns, d)
        level = nxt
        print(f'  {d} rotation(s): {len(nxt)} new valid states; largest total (slots minus forced agents) '
              f'{worst.get(d)}; proof bound 2d - t = {2 * d - t}', flush=True)
    print(f'  every structural step of the proof holds on all {len(seen)} states: {not bad}' + (f' {bad[:3]}' if bad else ''))
    return not bad and all(w <= 2 * d - t for d, w in worst.items())

if __name__ == '__main__':
    t, Q = int(sys.argv[1]), int(sys.argv[2])
    print(f'H3_{t} (variant A): reachable states with at most {Q} rotations', flush=True)
    r = reach(t, Q)
    print('all checks pass' if r else 'SOME CHECK FAILED')
