"""Replay of attempts/k4-gap-btcyc.md: #52's conjecture K4.HALL.BTCYC fails on a pure n = 4 profile.
Checks, with both k4/gap.c (-C dump) and k4/gap_model.py:
  - the profile is in the gap, f = 2, omega = 2, and the keys are the three listed (neither implementation has a key
    with agents 2 and 3 frozen on goods 2 and 3);
  - the configuration P (key [2, 3, -, -], Q_2 = {4, 7}, Q_3 = {1, 5}, L = {0, 6}) has no valid owner, and its
    pre-allocation is not removal-only completable;
  - P is Pareto-maximal among the configurations of the profile, and its frozen agents 0 and 1 are exposed big-top
    agents;
then, with gap_model: the exchange digraph of P has one cycle through them, (0, 2, 1, 3); no cycle move through it
(best pairs in every order, any admissible pairs, receivers keeping part of their pair) gives a configuration at the
fewest frozen agents, so none gives a completable pre-allocation; downgrade swaps do.
Usage: python3 attempts/k4_gap_btcyc.py (exit status 0 if every check passes)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'k4'))
import gap_model as gm, gap_bench as gb

SETS = [[0, 2, 5, 6], [0, 3, 4, 6], [1, 2, 4, 7], [1, 3, 5, 7]]
VALS = [[3, 10, 2, 6], [2, 10, 3, 6], [2, 10, 3, 6], [2, 8, 3, 4]]
M = 8
KEY, Q = (2, 3, None, None), {2: frozenset({4, 7}), 3: frozenset({1, 5})}

def main():
    ok = True
    rec = {'core': {'sets': SETS, 'm': M, 'file': 'btcyc', 'pos': 0, 'idx': 0}, 'vals': VALS, 'prof': [0] * 4}
    for _, head, cl in gb.dump([rec]):
        d = [x for x in cl if x['key'] == [2, 3, -1, -1] and x['Q'][2] == [4, 7] and x['Q'][3] == [1, 5]]
        vec = lambda x: tuple(x['phi'])
        print(f"gap.c: f {head['f']}, omega {head['omega']}, keys {head['keys']}; P: {d[0] if d else 'MISSING'}")
        ok &= head['f'] == 2 and head['omega'] == 2 and [-1, -1, 2, 3] not in head['keys'] and bool(d) and not d[0]['own']
    P = gm.Profile(SETS, VALS, M)
    cfgs = P.configs()
    for c in cfgs: c._phi_c = c.phi; c._own_c = c.owners
    c = [x for x in cfgs if x.key == KEY and x.Q == Q][0]
    par = gb.pareto(cfgs)
    X = [x for x in c.frozen if c.bigtop(x) and not c.robust(x)]
    print(f"gap_model: in the gap {P.in_gap}, f {P.f}, omega {P.omega}, keys {P.keys}")
    print(f"  P = {c}: valid owner {c.completable}, pre-allocation removal-only completable {c.p_completable}, "
          f"Pareto-maximal {c in par}, exposed frozen big-top agents {X}, threats {[(o, x, c.h7(x, o)) for o, x in c.threat_edges]}")
    ok &= P.in_gap and (None, None, 2, 3) not in P.keys and not c.completable and not c.p_completable and c in par and X == [0, 1]
    cyc = [cy for cy in c.cycles() if any(x in cy for x in X)]
    moves = [(cy, c2) for cy, c2 in c.cycle_moves() + c.cycle_moves(general=True) + c.cycle_moves(general=True, keep=True)
             if any(x in cy for x in X)]
    swaps = c.downgrade_swaps()
    print(f"  cycles through them: {cyc}; cycle moves with a min-frozen result: {len(moves)}; "
          f"downgrade swaps: {len(swaps)}, with a valid owner: {sum(s.completable for _, _, s in swaps)}")
    ok &= cyc == [[0, 2, 1, 3]] and not moves and any(s.completable for _, _, s in swaps)
    print("BTCYC fails on this profile (both implementations)" if ok else "MISMATCH")
    return 0 if ok else 1

if __name__ == '__main__':
    sys.exit(main())
